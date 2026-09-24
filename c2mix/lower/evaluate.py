"""Evaluate emitted statements on one concrete execution.

This is the machinery behind A1.3 and, later, gate G3: take a real run of the IR,
give every symbol the value it has in that run, and check that every statement the
lowering emitted is true. BV and Int parts follow the SMT-LIB semantics; Poly terms
follow §8.0, which for statements without indeterminates is plain integer equality.

A statement that is false here means the lowering is wrong (or the run violates a
precondition the analysis was given).
"""
from __future__ import annotations

from ..ir.interp import interpret
from ..spec.evalspec import Poly as _P
from .encode import Segment


class EvalError(Exception):
    pass


class Env:
    """Symbol values: bit patterns for BV symbols, integers for Int aliases, and
    polynomials for ghosts (sort (Poly Int))."""

    def __init__(self, bv: dict[str, int], widths: dict[str, int],
                 ints: dict[str, int] | None = None, polys: dict | None = None):
        self.bv = dict(bv)
        self.widths = dict(widths)
        self.ints = dict(ints or {})
        self.polys = dict(polys or {})


def _mask(w: int) -> int:
    return (1 << w) - 1


def eval_term(term, env: Env):
    """Iterative post-order evaluation. Returns ('bv', value, width) | ('int', v) | ('bool', b)."""
    stack = [(term, False)]
    vals: list[tuple] = []
    while stack:
        node, expanded = stack.pop()
        if isinstance(node, str):
            vals.append(_atom(node, env))
            continue
        if not expanded:
            stack.append((node, True))
            head = node[0]
            args = node[1:] if not isinstance(head, list) else node[1:]
            for a in reversed(args):
                stack.append((a, False))
            continue
        head = node[0]
        n = len(node) - 1
        args = [vals.pop() for _ in range(n)][::-1]
        vals.append(_apply(head, args, env))
    if len(vals) != 1:
        raise EvalError(f"could not evaluate {term}")
    return vals[0]


def _atom(tok: str, env: Env):
    if tok.startswith("#x"):
        return ("bv", int(tok[2:], 16), 4 * len(tok[2:]))
    if tok.startswith("#b"):
        return ("bv", int(tok[2:], 2), len(tok) - 2)
    if tok.isdigit():
        return ("int", int(tok))
    if tok == "true":
        return ("bool", True)
    if tok == "false":
        return ("bool", False)
    if tok in env.bv:
        return ("bv", env.bv[tok], env.widths[tok])
    if tok in env.ints:
        return ("int", env.ints[tok])
    if tok in env.polys:
        return ("poly", env.polys[tok])
    if tok.startswith('"') and tok.endswith('"'):
        return ("name", tok[1:-1])
    raise EvalError(f"unknown symbol {tok}")


def _as_int(v) -> int:
    if v[0] == "int":
        return v[1]
    raise EvalError(f"expected Int, got {v[0]}")


def _as_bv(v) -> tuple[int, int]:
    if v[0] == "bv":
        return v[1], v[2]
    raise EvalError(f"expected BV, got {v[0]}")


def _apply(head, args, env: Env):
    if isinstance(head, list):                      # indexed identifier
        kind = head[1]
        if kind == "extract":
            hi, lo = int(head[2]), int(head[3])
            x, _ = _as_bv(args[0])
            return ("bv", (x >> lo) & _mask(hi - lo + 1), hi - lo + 1)
        if kind in ("zero_extend", "sign_extend"):
            by = int(head[2])
            x, w = _as_bv(args[0])
            if kind == "sign_extend" and x >> (w - 1):
                x |= _mask(w + by) ^ _mask(w)
            return ("bv", x, w + by)
        raise EvalError(f"unsupported indexed operator {head}")

    if head == "bv2nat":
        x, _ = _as_bv(args[0])
        return ("int", x)
    if head == "bv2int":                            # z3 reads bv2int as unsigned (F3)
        x, _ = _as_bv(args[0])
        return ("int", x)
    if head in ("+", "-", "*"):
        if head == "-" and len(args) == 1:
            return ("int", -_as_int(args[0]))
        a, b = _as_int(args[0]), _as_int(args[1])
        return ("int", a + b if head == "+" else a - b if head == "-" else a * b)
    if head in ("bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor"):
        (a, w), (b, _) = _as_bv(args[0]), _as_bv(args[1])
        r = {"bvadd": a + b, "bvsub": a - b, "bvmul": a * b,
             "bvand": a & b, "bvor": a | b, "bvxor": a ^ b}[head]
        return ("bv", r & _mask(w), w)
    if head in ("bvneg", "bvnot"):
        a, w = _as_bv(args[0])
        return ("bv", (-a if head == "bvneg" else ~a) & _mask(w), w)
    if head in ("bvshl", "bvlshr", "bvashr"):
        (a, w), (k, _) = _as_bv(args[0]), _as_bv(args[1])
        if head == "bvshl":
            return ("bv", (a << k) & _mask(w), w)
        if head == "bvlshr":
            return ("bv", a >> k, w)
        return ("bv", (interpret(a, w, True) >> k) & _mask(w), w)
    if head in ("bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"):
        (a, w), (b, _) = _as_bv(args[0]), _as_bv(args[1])
        s = head[2] == "s"
        x, y = (interpret(a, w, True), interpret(b, w, True)) if s else (a, b)
        return ("bool", {"lt": x < y, "le": x <= y, "gt": x > y, "ge": x >= y}[head[3:]])
    if head == "=":
        a, b = args
        if a[0] == "bool":
            return ("bool", a[1] == b[1])
        return ("bool", a[1] == b[1] if a[0] == b[0] else False)
    if head == "distinct":
        return ("bool", args[0][1] != args[1][1])
    if head == "and":
        return ("bool", all(a[1] for a in args))
    if head == "or":
        return ("bool", any(a[1] for a in args))
    if head == "not":
        return ("bool", not args[0][1])
    if head == "ite":
        return args[1] if args[0][1] else args[2]
    # Poly terms: elements of ℤ[X] per §8.0
    if head == "PVar":
        if args[0][0] != "name":
            raise EvalError("PVar takes a string literal (M4)")
        return ("poly", _P.x(args[0][1]))
    if head == "PConst":
        return ("poly", _poly(args[0]))
    if head == "PAdd":
        return ("poly", _poly(args[0]) + _poly(args[1]))
    if head == "PSub":
        return ("poly", _poly(args[0]) - _poly(args[1]))
    if head == "PMul":
        return ("poly", _poly(args[0]) * _poly(args[1]))
    if head == "PNeg":
        return ("poly", _P.const(0) - _poly(args[0]))
    if head == "PPow":
        return ("poly", _poly(args[0]) ** _as_int(args[1]))
    if head == "eqP":
        return ("bool", not (_poly(args[0]) - _poly(args[1])).coeffs)
    if head in ("eqmodP1", "eqmodP2"):
        return ("bool", _eqmod(_poly(args[0]) - _poly(args[1]), [_poly(a) for a in args[2:]]))
    raise EvalError(f"unsupported operator {head}")


def _poly(v):
    """Read a value as a polynomial (§8.0); integers are constant polynomials."""
    if v[0] == "poly":
        return v[1]
    if v[0] == "int":
        return _P.const(v[1])
    raise EvalError(f"expected a polynomial, got {v[0]}")


def _eqmod(diff, mods) -> bool:
    """§8.1: reduce by the monic polynomial moduli, then test divisibility by the
    integer one. Anything else has no decision procedure here."""
    from ..spec.evalspec import UnsupportedEval, rem_monic
    ints = [m for m in mods if m.is_const()]
    polys = [m for m in mods if not m.is_const()]
    for m in polys:
        diff = rem_monic(diff, m)
    if not ints:
        return not diff.coeffs
    if len(ints) > 1:
        raise UnsupportedEval("more than one integer modulus")
    q = ints[0].value()
    return all(c % q == 0 for c in diff.coeffs)


def widths_of(seg: Segment) -> dict[str, int]:
    return {n: int(s[2]) for n, s in seg.decls.items()
            if isinstance(s, list) and s[:2] == ["_", "BitVec"]}


def solve_definitions(seg: Segment, env: Env) -> Env:
    """Give witnesses and aliases the values their defining statements assign.
    Statements are in emission order, so one pass is enough."""
    for st in seg.bv:
        if not (isinstance(st, list) and st[0] == "=" and isinstance(st[1], str)):
            continue
        name = st[1]
        if name in env.bv or name in env.ints:
            continue
        val = eval_term(st[2], env)
        if val[0] == "bv":
            env.bv[name] = val[1]
            env.widths[name] = val[2]
        else:
            env.ints[name] = val[1]
    return env


def check_segment(seg: Segment, env: Env) -> list[str]:
    """Every emitted statement must hold on this run. Returns the failures."""
    from ..mixfmt.writer import to_str
    bad = []
    for kind, statements in (("range", seg.bv), ("algebraic", seg.alg), ("safety", seg.safety)):
        for st in statements:
            got = eval_term(st, env)
            if got[0] != "bool":
                bad.append(f"{kind}: not a formula: {to_str(st)[:120]}")
            elif not got[1]:
                bad.append(f"{kind}: false on this run: {to_str(st)[:160]}")
    return bad
