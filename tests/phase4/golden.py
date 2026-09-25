"""A4.2 — the mathematical-layer comparison with the two goldens (spec §8.3, §9 phase 4).

The goldens come from assembly, c2mix's input is C, so nothing is compared as text.
What is compared is the proposition:

  Kyber   the modulus set of every layer (appendix C.4's method), the bound sequence
          q, 2q, …, 8q, and the conjunct counts 2, 4, …, 128;
  P-256   for each fiat function and its OpenSSL counterpart: the predicate (eqmodP1),
          the modulus, the limb weights, the Montgomery factor, and the range
          precondition 0 ≤ A < p.

Post-conditions are compared as relations, not as terms. Both sides are evaluated at
random limb values; the golden's lhs − rhs must equal a fixed unit times ours, modulo
p, at every point. That is exactly "the two congruences say the same thing", and it
does not care that OpenSSL's sub is written c + b ≡ a where fiat's is out ≡ a − b.
"""
from __future__ import annotations

import random
import re
from pathlib import Path

from c2mix.mixfmt import reader

MOD = re.compile(r'\(PConst (\d+)\) \(PSub \(PPow (?:\(PVar "x(?:_0)?"\)|\(PConst \(bv2nat x_0\)\)) '
                 r'(\d+)\) \(PConst (\d+)\)\)')


# ------------------------------------------------------------------------- Kyber
def kyber_moduli(files: list[Path]) -> dict[int, set[int]]:
    """{degree: {zeta}} over the postconditions of these mix files."""
    out: dict[int, set[int]] = {}
    for f in files:
        post = f.read_text().split("; postcondition")[1]
        for q, d, c in MOD.findall(post):
            out.setdefault(int(d), set()).add(int(c))
    return out


def kyber(golden_dir: Path, ours: list[Path], spec, q: int) -> tuple[bool, str]:
    gold = kyber_moduli(sorted(golden_dir.glob("cut*.smt2")))
    mine = kyber_moduli(ours)
    notes, ok = [], True
    if set(gold) != set(mine):
        ok = False
        notes.append(f"degrees differ: golden {sorted(gold)}, ours {sorted(mine)}")
    for d in sorted(set(gold) & set(mine)):
        if gold[d] != mine[d]:
            ok = False
            notes.append(f"degree {d}: {len(gold[d] ^ mine[d])} modulus/moduli differ")
    # bounds and conjunct counts, read off the specification's cuts
    bounds, counts = [], []
    for c in spec.cut_list:
        his = {_const(a.hi) for a in c.ranges}
        bounds.append(max(his) // q if len(his) == 1 else None)
        counts.append(len(c.algs))
    pre = {_const(a.hi) for a in spec.pre_ranges}
    seq = [max(pre) // q] + bounds
    want_seq = list(range(1, len(spec.cut_list) + 2))
    want_counts = [2 ** k for k in range(1, len(spec.cut_list) + 1)]
    if seq != want_seq:
        ok = False
        notes.append(f"bounds {seq}·q, want {want_seq}·q")
    if counts != want_counts:
        ok = False
        notes.append(f"conjuncts {counts}, want {want_counts}")
    summary = (f"{len(gold)} layers, moduli per layer {[len(mine.get(d, ())) for d in sorted(mine, reverse=True)]}"
               f", bounds {seq}·q, conjuncts {counts}")
    return ok, summary + ("" if ok else "; " + "; ".join(notes))


def _const(e) -> int:
    from c2mix.vc.terms import const_value
    v = const_value(e)
    if v is None:
        raise ValueError(f"{e} is not constant")
    return v


# ------------------------------------------------------------------------- P-256
def _asserts(path: Path, section: str) -> list:
    mix = reader.read(path)
    secs = mix.sections()
    return [c.sexpr for c in secs[section] if isinstance(c, reader.Command)
            and isinstance(c.sexpr, list) and c.sexpr[0] == "assert"]


def _goal(path: Path):
    """The congruence under (assert (not …))."""
    term = _asserts(path, "post")[0][1]
    assert term[0] == "not"
    goal = term[1]
    while isinstance(goal, list) and goal[0] == "and":      # c2mix writes (and <A>) (M6)
        rest = [g for g in goal[1:] if g != "true"]
        if len(rest) != 1:
            break
        goal = rest[0]
    return goal


def _poly_eval(t, env: dict) -> int:
    """Integer value of a Poly term with no indeterminates."""
    if isinstance(t, str):
        if t.lstrip("-").isdigit():
            return int(t)
        return env[t]
    head = t[0]
    if head == "PConst":
        return _poly_eval(t[1], env)
    if head == "bv2nat":
        return env[t[1]]
    if head == "-":
        return -_poly_eval(t[1], env) if len(t) == 2 else _poly_eval(t[1], env) - _poly_eval(t[2], env)
    args = [_poly_eval(a, env) for a in t[1:]]
    if head == "PAdd":
        return args[0] + args[1]
    if head == "PSub":
        return args[0] - args[1]
    if head == "PMul":
        return args[0] * args[1]
    if head == "PNeg":
        return -args[0]
    if head == "PPow":
        return args[0] ** args[1]
    raise ValueError(f"unexpected {head}")


def _symbols(t, out: set) -> set:
    if isinstance(t, str):
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", t):
            out.add(t)
    else:
        for a in t:
            _symbols(a, out)
    return out


GOLD_NAME = re.compile(r"^([a-z])(\d)_(\d+)$")          # a0_0, c3_1, m2_0
ROLE = {"a": "arg1", "b": "arg2", "c": "out1"}


def roles(trace, names=("arg1", "arg2", "out1")) -> dict:
    """{SMT name: (object, index)} for our side: entry values of the arguments, exit
    values of the result — read off the trace, since a result limb is whatever SSA
    value was stored last (`t81`), not a name that says so."""
    from c2mix.ir.trace import ENTRY_POINT, EXIT_POINT
    out = {}
    for obj in names:
        if obj not in trace.objects:
            continue
        point = EXIT_POINT if obj.startswith("out") else ENTRY_POINT
        for i in range(trace.objects[obj].count):
            out[trace.value(point, obj, i).name] = (obj, i)
    return out


_ROLES: dict = {}


def _role(sym: str):
    """(object, index) for a limb symbol of either side, or None."""
    if sym in _ROLES:
        return _ROLES[sym]
    m = GOLD_NAME.match(sym)
    if m and m.group(1) in ROLE:
        return ROLE[m.group(1)], int(m.group(2))
    return None


def golden_modulus(path: Path) -> int:
    """m from the golden's range precondition: (= m0_0 #x…) ∧ …"""
    text = path.read_text().split("; algebraic precondition")[0]
    limbs = {int(i): int(v, 16) for i, v in re.findall(r"\(= m(\d)_0 #x([0-9A-Fa-f]+)\)", text)}
    return sum(v << (64 * i) for i, v in limbs.items())


def p256_post(golden: Path, ours: Path, p: int, ours_roles: dict,
              samples: int = 6) -> tuple[bool, str]:
    _ROLES.clear()
    _ROLES.update(ours_roles)
    g, o = _goal(golden), _goal(ours)
    if g[0] != "eqmodP1" or o[0] != "eqmodP1":
        return False, f"predicates {g[0]} vs {o[0]}"
    m_gold = golden_modulus(golden)
    rng = random.Random(4)
    gsyms, osyms = _symbols(g[1:3], set()), _symbols(o[1:3], set())
    inner = sorted(x for x in gsyms if _role(x) is None and not re.fullmatch(r"m\d_0", x)
                   and x not in ("PConst", "PAdd", "PSub", "PMul", "PPow", "PNeg", "bv2nat"))
    if inner:
        # a golden cut in the middle of the function: its post is about registers the
        # C program has no counterpart for; the later file carries the input/output
        # relation, so only the predicate and the modulus are compared here
        ok = m_gold == p
        return ok, (f"eqmodP1, {'same p' if ok else 'different modulus'}; post over "
                    f"intermediate registers ({', '.join(inner[:3])}…), relation compared "
                    f"in the file that ends the function")
    unit = None
    for _ in range(samples):
        limbs = {}
        genv, oenv = {}, {}
        for s in sorted(gsyms | osyms):
            role = _role(s)
            if role is None:
                continue
            limbs.setdefault(role, rng.randrange(1 << 64))
            (genv if s in gsyms else oenv)[s] = limbs[role]
        genv.update({f"m{i}_0": (m_gold >> (64 * i)) & ((1 << 64) - 1) for i in range(4)})
        fg = (_poly_eval(g[1], genv) - _poly_eval(g[2], genv)) % p
        fo = (_poly_eval(o[1], oenv) - _poly_eval(o[2], oenv)) % p
        mod_o = _poly_eval(o[3], oenv)
        if mod_o != p or m_gold != p:
            return False, f"modulus: golden {hex(m_gold)}, ours {hex(mod_o)}, p {hex(p)}"
        if fo == 0:
            continue
        u = fg * pow(fo, -1, p) % p
        if unit is None:
            unit = u
        elif u != unit:
            return False, "the two congruences are not multiples of each other"
    if unit is None:
        return False, "no sample separated the two sides"
    shown = "1" if unit == 1 else ("−1" if unit == p - 1 else "a unit")
    return True, f"eqmodP1, same p, golden = {shown} × ours"


def _range_pre(path: Path):
    return _asserts(path, "range")[0][1]


def p256_pre(golden: Path, ours: Path, p: int, ours_roles: dict) -> tuple[bool, str]:
    """Does the golden's range precondition accept the same inputs as ours? Both are
    evaluated where it matters: A (and B) at 0, 1, p − 1, p, p + 1 and 2²⁵⁶ − 1."""
    from c2mix.lower import evaluate
    _ROLES.clear()
    _ROLES.update(ours_roles)
    g, o = _range_pre(golden), _range_pre(ours)
    gsyms, osyms = _symbols(g, set()), _symbols(o, set())
    m = golden_modulus(golden)
    points = [0, 1, p - 1, p, p + 1, (1 << 256) - 1]
    binary = any(_role(s) == ("arg2", 0) for s in gsyms | osyms)
    table = []
    for a in points:
        for b in (points if binary else [0]):
            vals = {"arg1": a, "arg2": b}
            out = []
            for term, syms in ((g, gsyms), (o, osyms)):
                bv, widths = {}, {}
                for s_ in syms:
                    r = _role(s_)
                    if r and r[0] in vals:
                        bv[s_], widths[s_] = (vals[r[0]] >> (64 * r[1])) & ((1 << 64) - 1), 64
                    elif re.fullmatch(r"m\d_0", s_):
                        bv[s_], widths[s_] = (m >> (64 * int(s_[1]))) & ((1 << 64) - 1), 64
                try:
                    got = evaluate.eval_term(term, evaluate.Env(bv, widths))
                except (KeyError, evaluate.EvalError) as e:
                    return False, f"cannot evaluate a range precondition: {e}"
                out.append(got[1])
            table.append(((a, b), out[0], out[1]))
    diff = [t for t in table if t[1] != t[2]]
    if not diff:
        return True, "same range precondition (0 ≤ A < p" + (", 0 ≤ B < p)" if binary else ")")
    (a, b), gv, ov = diff[0]
    name = {0: "0", 1: "1", p - 1: "p−1", p: "p", p + 1: "p+1", (1 << 256) - 1: "2²⁵⁶−1"}
    return False, (f"range preconditions differ at A={name[a]}" + (f", B={name[b]}" if binary else "")
                   + f": golden {'accepts' if gv else 'rejects'}, ours {'accepts' if ov else 'rejects'}")
