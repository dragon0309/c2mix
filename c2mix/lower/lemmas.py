"""Rule lemmas (A1.1) and their mutations (A1.2), generated from the rules themselves.

A lemma says: the range statements plus the safety obligations imply the algebraic
statements. It is written as an SMT2 file over BV and Int (appendix A), so `z3` must
answer `unsat`. Because the file comes out of `rules.py`, the lemma checks the code
that actually emits VCs, not a re-implementation of it.

A mutation breaks exactly one thing (a power of two, a signedness, a split term, a
bound) and must turn the lemma `sat`.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from ..ir import intervals as iv
from ..ir.ops import Builder, Program, Value
from ..mixfmt.reader import rewrite
from ..mixfmt.writer import to_str
from . import encode as E
from . import rules
from .encode import Encoder, Segment

LEMMA_WIDTHS = (4, 8, 16, 32, 64)
WIDE_WIDTH = 128                 # 128-bit: everything but mul (spec A1.1)


@dataclass
class Lemma:
    name: str
    rule: str
    expect: str                  # unsat for a lemma, sat for a mutant
    text: str
    mutation: str | None = None
    segment: "Segment | None" = field(default=None, repr=False)
    equivalent: str | None = None      # set when a mutation is certified as no-op
    site: tuple | None = None          # (value, width) a sign mutation was applied to
    dropped_safety: object = None      # the obligation a "safety" mutation removed
    variant: str = "mixed"             # mixed: the encoding c2mix emits; bv: QF_BV image
    inputs: frozenset = field(default_factory=frozenset, repr=False)


# ---------------------------------------------------------------- Poly -> Int
def poly_to_int(term):
    """Translate a Poly term to plain Int arithmetic; eqP becomes =.
    Only used for lemmas, which have no indeterminates."""
    def fn(n):
        if not isinstance(n, list) or not n:
            return None
        head = n[0]
        if head == "PConst":
            return n[1]
        if head == "PAdd":
            return ["+", n[1], n[2]]
        if head == "PSub":
            return ["-", n[1], n[2]]
        if head == "PMul":
            return ["*", n[1], n[2]]
        if head == "PNeg":
            return ["-", n[1]]
        if head == "PPow":
            k = int(n[2])
            return ["*"] + [n[1]] * k if k > 1 else n[1]
        if head == "eqP":
            return ["=", n[1], n[2]]
        if head == "PVar":
            raise ValueError("lemmas must not contain indeterminates")
        return None
    return rewrite(term, fn)


def _bv_widths(seg: Segment) -> dict[str, int]:
    return {n: int(sort[2]) for n, sort in seg.decls.items()
            if isinstance(sort, list) and sort[:2] == ["_", "BitVec"]}


def poly_to_bv(term, N: int, widths: dict[str, int]):
    """Image of an algebraic statement in QF_BV at width N.

    ⟦v⟧ becomes v extended to N bits — zero_extend for the unsigned reading,
    sign_extend for the signed one — and the Int operations become their BV
    counterparts. With N wider than any value the statement can take (we use
    2·max width + 8), N-bit equality holds exactly when the Int equation does, so
    this is the same lemma in a theory z3 can bit-blast. The mixed-encoding lemma
    (the encoding c2mix really emits) is checked at width 4, where z3 manages it.
    """
    def atom(n):
        if isinstance(n, str):
            if n.startswith("s__"):
                v = n[3:]
                return E.extend("sign_extend", N - widths[v], v)
            if n.isdigit():
                return E.bv_const(int(n), N)
            return None
        if n[:1] == ["bv2nat"] and isinstance(n[1], str):
            return E.extend("zero_extend", N - widths[n[1]], n[1])
        if n[:1] == ["bv2nat"]:                       # (bv2nat ((_ extract i i) v))
            return E.extend("zero_extend", N - 1, n[1])
        if n[:1] == ["-"] and len(n) == 2 and isinstance(n[1], str) and n[1].isdigit():
            return E.bv_const(-int(n[1]), N)
        return None

    def fn(n):
        got = atom(n)
        if got is not None:
            return got
        if not isinstance(n, list) or not n:
            return None
        head = n[0]
        if head == "PConst":
            return n[1]
        if head == "PAdd":
            return ["bvadd", n[1], n[2]]
        if head == "PSub":
            return ["bvsub", n[1], n[2]]
        if head == "PMul":
            return ["bvmul", n[1], n[2]]
        if head == "PNeg":
            return ["bvneg", n[1]]
        if head == "-" and len(n) == 2:            # unary minus from an Int literal
            return ["bvneg", n[1]]
        if head == "-" and len(n) == 3:            # two's-complement formula (sign mutant)
            return ["bvsub", n[1], n[2]]
        if head == "*" and len(n) == 3:
            return ["bvmul", n[1], n[2]]
        if head == "eqP":
            return ["=", n[1], n[2]]
        if head == "PPow":
            k = int(n[2])
            out = n[1]
            for _ in range(k - 1):
                out = ["bvmul", out, n[1]]
            return out
        if head == "PVar":
            raise ValueError("lemmas must not contain indeterminates")
        return None
    return rewrite(term, fn)


def render_bv(lemma: Lemma) -> Lemma:
    """The same lemma, stated in QF_BV (see poly_to_bv)."""
    seg = lemma.segment
    widths = _bv_widths(seg)
    N = 2 * max(widths.values()) + 8
    lines = ["(set-info :smt-lib-version 2.0)", "(set-logic QF_BV)"]
    for n, sort in seg.decls.items():
        if n in widths:
            lines.append(to_str(["declare-const", n, sort]))
    for t in seg.bv:
        if isinstance(t, list) and t[0] == "=" and isinstance(t[1], str) and t[1] not in widths:
            continue                                   # Int alias definition: not needed here
        lines.append(to_str(["assert", t]))
    for t in seg.safety:
        lines.append(to_str(["assert", t]))
    goal = [poly_to_bv(t, N, widths) for t in seg.alg]
    body = goal[0] if len(goal) == 1 else ["and"] + goal
    lines += [to_str(["assert", ["not", body]]), "(check-sat)", "(exit)"]
    out = Lemma(lemma.name, lemma.rule, lemma.expect, "\n".join(lines) + "\n",
                lemma.mutation, seg, inputs=lemma.inputs)
    out.site, out.variant = lemma.site, "bv"
    out.dropped_safety = lemma.dropped_safety
    return out


# ---------------------------------------------------------------- building
def forced(prog: Program, decision: str, pre: dict | None = None) -> iv.Analysis:
    """Analysis with every overflowing instruction forced to one decision, so a lemma
    can be generated for the EXACT and the SPLIT form of the same rule."""
    an = iv.analyze(prog, pre)
    for idx, ins in enumerate(prog.instrs):
        if an.decisions.get(idx) in (iv.EXACT, iv.SPLIT):
            an.decisions[idx] = decision
            if decision == iv.SPLIT and ins.result is not None:
                an.intervals[ins.result.name] = iv.full(ins.result)
    return an


def render(seg: Segment, name: str, rule: str, mutation: str | None = None,
           expect: str = "unsat") -> Lemma:
    lines = ["(set-info :smt-lib-version 2.0)", "(set-logic ALL)"]
    for n, sort in seg.decls.items():
        lines.append(to_str(["declare-const", n, sort]))
    for t in seg.bv:
        lines.append(to_str(["assert", t]))
    for t in seg.safety:
        lines.append(to_str(["assert", t]))
    goal = [poly_to_int(t) for t in seg.alg]
    if not goal:
        raise ValueError(f"{name}: no algebraic statement to prove")
    body = goal[0] if len(goal) == 1 else ["and"] + goal
    lines += [to_str(["assert", ["not", body]]), "(check-sat)", "(exit)"]
    return Lemma(name, rule, expect, "\n".join(lines) + "\n", mutation, seg)


def _lemma(name, rule, build, decision=None, pre=None) -> Lemma:
    """build(Builder) -> Program; lowered with `decision` forced when given."""
    b = Builder()
    prog = build(b)
    an = forced(prog, decision, pre) if decision else iv.analyze(prog, pre)
    seg = rules.lower(prog, an)
    L = render(seg, name, rule)
    L.inputs = frozenset(v.name for v in prog.inputs)
    return L


# ---------------------------------------------------------------- the catalogue
def generate(widths=LEMMA_WIDTHS) -> list[Lemma]:
    out: list[Lemma] = []
    for w in widths:
        for signed in (True, False):
            s = "s" if signed else "u"
            tag = f"w{w}.{s}"

            def two(b, width=w, sign=signed):
                return b.input("a", width, sign), b.input("b", width, sign)

            for op, rule in (("add", "L3"), ("sub", "L3"), ("neg", "L3")):
                def build(b, op=op, width=w, sign=signed):
                    a, bb = two(b, width, sign)
                    b.binop(op, a, bb) if op != "neg" else b.neg(a)
                    return b.build()
                out.append(_lemma(f"{rule}.{op}.{tag}", rule, build, iv.EXACT))
                out.append(_lemma(f"{rule}p.{op}.{tag}", rule + "'", build, iv.SPLIT))

            if w <= 64:
                def bmul(b, width=w, sign=signed):
                    a, bb = two(b, width, sign)
                    b.mul(a, bb)
                    return b.build()
                out.append(_lemma(f"L4.{tag}", "L4", bmul, iv.EXACT))
                out.append(_lemma(f"L4p.{tag}", "L4'", bmul, iv.SPLIT))

            for k in (1, w // 2):
                def bshl(b, k=k, width=w, sign=signed):
                    b.shl(b.input("a", width, sign), k)
                    return b.build()
                out.append(_lemma(f"L6.k{k}.{tag}", "L6", bshl, iv.EXACT))
                out.append(_lemma(f"L6p.k{k}.{tag}", "L6'", bshl, iv.SPLIT))

                def bshr(b, k=k, width=w, sign=signed):
                    a = b.input("a", width, sign)
                    b.ashr(a, k) if sign else b.lshr(a, k)
                    return b.build()
                out.append(_lemma(f"L7.k{k}.{tag}", "L7", bshr))

            if 2 * w <= 128:
                def bext(b, width=w, sign=signed):
                    a = b.input("a", width, sign)
                    b.sext(a, 2 * width) if sign else b.zext(a, 2 * width)
                    return b.build()
                out.append(_lemma(f"L8.{tag}", "L8", bext))

            if w >= 8:
                half = w // 2

                def bnarrow(b, width=w, half=half, sign=signed):
                    b.extract(b.input("a", width, sign), half - 1, 0, signed=sign)
                    return b.build()
                out.append(_lemma(f"L9.{tag}", "L9", bnarrow, iv.EXACT))
                out.append(_lemma(f"L9p.{tag}", "L9'", bnarrow, iv.SPLIT))

                def bfield(b, width=w, half=half, sign=signed):
                    b.extract(b.input("a", width, sign), width - 2, 1, signed=sign)
                    return b.build()
                out.append(_lemma(f"L11.{tag}", "L11", bfield))

                def bmask(b, width=w, half=half, sign=signed):
                    a = b.input("a", width, sign)
                    m = b.const((1 << half) - 1, width, sign)
                    b.and_(a, m)
                    return b.build()
                out.append(_lemma(f"L9m.{tag}", "L9m", bmask))

            def bnot(b, width=w, sign=signed):
                b.not_(b.input("a", width, sign))
                return b.build()
            out.append(_lemma(f"L13n.{tag}", "L13n", bnot))

            def bite(b, width=w, sign=signed):
                c = b.input("c", 1, False)
                x, y = b.input("x", width, sign), b.input("y", width, sign)
                b.ite(c, x, y)
                return b.build()
            out.append(_lemma(f"L12.{tag}", "L12", bite))

            def bcmov(b, width=w, sign=signed):
                """L12's mask form: the branch-free conditional move (§6.3). The
                obligation that the mask is all ones or all zero is part of the
                lemma's premises, exactly as it is part of the range VC."""
                c = b.input("c", 1, False)
                m = b.neg(b.zext(c, width))       # the mask the analysis recognises
                x, y = b.input("x", width, sign), b.input("y", width, sign)
                b.or_(b.and_(m, x), b.and_(b.not_(m), y))
                return b.build()
            out.append(_lemma(f"L12m.{tag}", "L12", bcmov))

            out.append(_bridge_lemma(w, signed, f"L10.{tag}"))

    # 128-bit: everything except mul (A1.1)
    for signed in (True, False):
        tag = f"w{WIDE_WIDTH}.{'s' if signed else 'u'}"
        for op, rule in (("add", "L3"), ("sub", "L3")):
            def build(b, op=op, sign=signed):
                a = b.input("a", WIDE_WIDTH, sign)
                bb = b.input("b", WIDE_WIDTH, sign)
                b.binop(op, a, bb)
                return b.build()
            out.append(_lemma(f"{rule}.{op}.{tag}", rule, build, iv.EXACT))
            out.append(_lemma(f"{rule}p.{op}.{tag}", rule + "'", build, iv.SPLIT))

        def bshift(b, sign=signed):
            a = b.input("a", WIDE_WIDTH, sign)
            b.ashr(a, 64) if sign else b.lshr(a, 64)
            return b.build()
        out.append(_lemma(f"L7.k64.{tag}", "L7", bshift))

        def bnarrow(b, sign=signed):
            b.extract(b.input("a", WIDE_WIDTH, sign), 63, 0, signed=sign)
            return b.build()
        out.append(_lemma(f"L9.{tag}", "L9", bnarrow, iv.EXACT))
        out.append(_lemma(f"L9p.{tag}", "L9'", bnarrow, iv.SPLIT))
    return out


def _bridge_lemma(w: int, signed: bool, name: str) -> Lemma:
    """L10 on its own: the two readings of one value, related by the sign bit."""
    seg = Segment()
    enc = Encoder(seg)
    v = Value("v", w, signed, "input")
    enc.declare(v)
    enc.both(v)
    return render(seg, name, "L10")


# ---------------------------------------------------------------- mutations
def _widths(seg: Segment) -> dict[str, int]:
    return {n: int(sort[2]) for n, sort in seg.decls.items()
            if isinstance(sort, list) and sort[:2] == ["_", "BitVec"]}


def _iter(term):
    from ..mixfmt.reader import iter_nodes
    return iter_nodes(term)


def _find(term, pred):
    """First sub-term (pre-order) satisfying pred."""
    from ..mixfmt.reader import iter_nodes
    for n in iter_nodes(term):
        if pred(n):
            return n
    return None


def _replace_once(term, target, repl):
    """Replace the first occurrence of `target` (by value) with `repl`."""
    done = []

    def fn(n):
        if not done and n == target:
            done.append(True)
            return repl
        return None
    out = rewrite(term, fn)
    return out if done else None


def _is_pow2_literal(n) -> bool:
    return isinstance(n, str) and n.isdigit() and int(n) >= 2 and int(n) & (int(n) - 1) == 0


def _mutants(seg: Segment, name: str, rule: str, inputs: frozenset[str] = frozenset()) -> list[Lemma]:
    """A1.2: one broken thing per mutant; each must turn the lemma sat."""
    widths = _widths(seg)
    out = []
    # Mutate what the rule itself asserts; the L10 bridges the encoder adds along the
    # way are incidental here and each has its own lemma.
    targets = [i for i in range(len(seg.alg)) if i not in seg.bridge_alg] or list(range(len(seg.alg)))

    def emit(kind, alg=None, safety=None, site=None):
        m = Segment(dict(seg.decls), list(seg.bv), alg if alg is not None else list(seg.alg),
                    safety if safety is not None else list(seg.safety), list(seg.notes))
        L = render(m, f"{name}.{kind}", rule, mutation=kind, expect="sat")
        L.site = site
        out.append(L)

    # a power of two is wrong
    for i, t in ((i, seg.alg[i]) for i in targets):
        lit = _find(t, _is_pow2_literal)
        if lit is not None:
            alg = list(seg.alg)
            alg[i] = _replace_once(t, lit, str(int(lit) * 2))
            emit("scale", alg=alg)
            break

    # one operand is read with the wrong signedness; prefer an input, whose two
    # readings are not constrained to agree by the rest of the lemma
    def sign_sites(t, only_inputs):
        def ok(v):
            return (not only_inputs or v in inputs) and widths.get(v, 0) > 1
        for n in _iter(t):
            if isinstance(n, str) and n.startswith("s__") and ok(n[3:]):
                yield n, ["bv2nat", n[3:]]
            elif (isinstance(n, list) and len(n) == 2 and n[0] == "bv2nat"
                  and isinstance(n[1], str) and ok(n[1])):
                w = widths[n[1]]
                yield n, ["-", n, ["*", str(1 << w),
                                   ["bv2nat", E.extract(w - 1, w - 1, n[1])]]]

    seen_sites: set[str] = set()
    for i, t in ((i, seg.alg[i]) for i in targets):
        for target, repl in sign_sites(t, only_inputs=False):
            v = target[3:] if isinstance(target, str) else target[1]
            if v in seen_sites or len(seen_sites) >= 4:
                continue
            seen_sites.add(v)
            alg = list(seg.alg)
            alg[i] = _replace_once(t, target, repl)
            emit(f"sign.{v}", alg=alg, site=(v, widths[v]))

    # a split term is missing
    for i, t in ((i, seg.alg[i]) for i in targets):
        add = _find(t, lambda n: isinstance(n, list) and n[:1] == ["PAdd"])
        if add is not None:
            alg = list(seg.alg)
            alg[i] = _replace_once(t, add, add[1])
            emit("drop", alg=alg)
            break

    # the equation is off by one
    j = targets[0]
    t = seg.alg[j]
    alg = list(seg.alg)
    alg[j] = E.eqP(E.PAdd(t[1], E.PInt(1)), t[2])
    emit("offbyone", alg=alg)

    # a safety bound is missing, so overflow is no longer ruled out
    if seg.safety:
        dropped = seg.safety[0]
        m = Segment(dict(seg.decls), list(seg.bv), list(seg.alg), list(seg.safety[1:]),
                    list(seg.notes))
        L = render(m, f"{name}.safety", rule, mutation="safety", expect="sat")
        L.dropped_safety = dropped
        out.append(L)
    return out


def mutate(lemma: Lemma, inputs: frozenset[str] = frozenset()) -> list[Lemma]:
    if lemma.segment is None:
        raise ValueError(f"{lemma.name}: no segment to mutate")
    return _mutants(lemma.segment, lemma.name, lemma.rule, inputs or lemma.inputs)


# ---------------------------------------------------------------- checking
def certify_equivalent(lemma: Lemma, z3_bin: str = "z3", timeout: float = 60) -> bool:
    """Some mutations cannot change anything, and z3 says which (A1.2/G7).

    A sign mutation cannot, when the lemma's own statements pin the value's sign bit:
    ask whether that bit can be 1 at all, and unsat means pinned. Dropping a safety
    obligation cannot, when the bit-vector statements already imply it — which is the
    case for the mask of L12's mask form, where the analysis recognised the mask from
    how it was built and the obligation only re-states what the definitions say."""
    if getattr(lemma, "dropped_safety", None) is not None and lemma.segment is not None:
        return _certify_redundant_safety(lemma, z3_bin, timeout)
    if lemma.site is None or lemma.segment is None:
        return False
    v, w = lemma.site
    seg = lemma.segment
    lines = ["(set-logic ALL)"]
    for n, sort in seg.decls.items():
        lines.append(to_str(["declare-const", n, sort]))
    for t in list(seg.bv) + list(seg.safety):
        lines.append(to_str(["assert", t]))
    lines += [to_str(["assert", ["=", E.extract(w - 1, w - 1, v), "#b1"]]), "(check-sat)"]
    probe = Lemma(lemma.name + ".probe", lemma.rule, "unsat", "\n".join(lines) + "\n")
    ok, _ = check(probe, z3_bin, timeout)
    if ok:
        lemma.equivalent = (f"the lemma's own statements force the sign bit of {v} to 0, "
                            "so both readings of it are equal")
    return ok


def _certify_redundant_safety(lemma: Lemma, z3_bin: str, timeout: float) -> bool:
    seg = lemma.segment
    lines = ["(set-logic ALL)"]
    for n, sort in seg.decls.items():
        lines.append(to_str(["declare-const", n, sort]))
    for t in list(seg.bv) + list(seg.safety[1:]):
        lines.append(to_str(["assert", t]))
    lines += [to_str(["assert", ["not", lemma.dropped_safety]]), "(check-sat)"]
    probe = Lemma(lemma.name + ".probe", lemma.rule, "unsat", "\n".join(lines) + "\n")
    ok, _ = check(probe, z3_bin, timeout)
    if ok:
        lemma.equivalent = ("the bit-vector statements already imply the dropped "
                            "obligation, so the range VC re-proves it rather than "
                            "assuming it")
    return ok


def check(lemma: Lemma, z3_bin: str = "z3", timeout: float = 120) -> tuple[bool, str]:
    """Run z3 on the lemma; returns (matches expectation, result)."""
    import subprocess
    try:
        p = subprocess.run([z3_bin, "-in", "-smt2"], input=lemma.text,
                           capture_output=True, text=True, timeout=timeout)
        raw = p.stdout + p.stderr
        if "(error" in raw:
            # never let a parse or sort error pass as an answer
            return False, "error: " + next(l for l in raw.splitlines() if "(error" in l)[:160]
        got = raw.strip().splitlines()
        got = got[-1].strip() if got else "no-output"
    except subprocess.TimeoutExpired:
        got = "timeout"
    return got == lemma.expect, got


def check_all(lemmas: list[Lemma], z3_bin: str = "z3", jobs: int = 8, timeout: float = 120):
    """Returns [(lemma, ok, result)], run in parallel (each z3 call is its own process)."""
    from concurrent.futures import ThreadPoolExecutor
    def one(L):
        ok, got = check(L, z3_bin, timeout)
        if not ok and L.expect == "sat" and got == "unsat" and certify_equivalent(L, z3_bin, timeout):
            return L, True, "unsat (equivalent mutation)"
        return L, ok, got
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        return list(pool.map(one, lemmas))
