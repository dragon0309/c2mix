"""Hint discovery (spec §6.4): range facts the algebraic layer cannot see.

Some algebraic proofs need a fact only the bit-vector model knows — the classic one is
that a Montgomery reduction's low half is zero. The candidates are

  H1 a low or high part from L7 / L9′ / L9m equal to a constant,
  H2 a mask that is all-zeros or all-ones,
  H3 any 1-bit symbol equal to a constant,
  H4 two 1-bit symbols that are always equal — the select condition of a conditional
     subtraction and the borrow of the subtraction it selects on are the same bit, but
     nothing in the algebraic model says so,
  H5 two SPLIT narrowings that throw away the same amount. A value computed at a wider
     type and stored back into a narrow one wraps; when the program then undoes the
     computation, the second wrap cancels the first, and the congruence only holds
     because of it. Barrett reduction is the standard case: `t *= q` wraps and `a - t`
     wraps back. CryptoLine writes this hint by hand (`assert (sext r 16) = a32 - tq`);
     here it is a candidate like any other,
  H6 a value equals the weighted sum of the one-bit symbols its own shifts produced.
     Bitwise operations and comparisons are algebraically free (L13), so a program that
     takes a value apart bit by bit — shift-and-add multiplication is the textbook case
     — leaves the algebraic model with no link at all between the value and the bits
     that were read out of it,

and a candidate becomes a hint only once z3 proves it from the segment's range model
plus the range premises. Candidates are first run past a few real executions: one that
some execution refutes cannot be proved, so it never costs a solver call. Soundness
does not rest on that proof alone: the range VC re-proves every emitted hint (G5), and
dropping a hint can only make the algebraic proof harder, never unsound.
"""
from __future__ import annotations

from dataclasses import dataclass

from ..ir.interp import interpret
from ..lower import encode as E
from ..lower import evaluate
from ..mixfmt.writer import to_str
from . import prover


def _reading(enc, name: str, width: int):
    """(atom, is the reading signed) for a symbol, following how it is read elsewhere:
    a copy's alias first (its own atom appears nowhere else), then the signed alias
    if the segment uses one, else the unsigned reading."""
    for signed in (False, True):
        if (name, signed) in enc._alias:
            return enc._alias[(name, signed)], signed
    if f"s__{name}" in enc.seg.decls:
        return f"s__{name}", True
    return ["bv2nat", name], False


@dataclass
class Hint:
    symbol: str
    width: int
    value: int
    kind: str          # H1 | H2 | H3

    def bv_term(self):
        return ["=", self.symbol, E.bv_const(self.value, self.width)]

    def poly_term(self, enc):
        atom, signed = _reading(enc, self.symbol, self.width)
        # the integer this bit pattern is in that reading: all ones read signed is −1
        return E.eqP(E.PConst(atom), E.PInt(interpret(self.value, self.width, signed)))

    def __str__(self):
        return f"{self.kind}: {self.symbol} = {self.value}"


@dataclass
class PairHint:
    """Two symbols that always hold the same bit pattern (H4)."""
    left: str
    right: str
    width: int
    kind: str = "H4"

    def bv_term(self):
        return ["=", self.left, self.right]

    def poly_term(self, enc):
        la, ls = _reading(enc, self.left, self.width)
        ra, rs = _reading(enc, self.right, self.width)
        if ls == rs:                                  # same reading: equal integers
            return E.eqP(E.PConst(la), E.PConst(ra))
        # one is read signed: for a 1-bit value the signed reading is the negated one
        return E.eqP(E.PAdd(E.PConst(la), E.PConst(ra)), E.PInt(0))

    def __str__(self):
        return f"{self.kind}: {self.left} = {self.right}"


@dataclass
class DropHint:
    """H5: two SPLIT narrowings drop the same amount, ⟦x⟧ − ⟦r⟧ = ⟦x′⟧ − ⟦r′⟧.

    Both terms are built while the hint is discovered, not while it is printed: asking
    the encoder for an atom can add an alias definition to the range model, and by
    printing time that section is already on disk."""
    left: dict
    right: dict
    bv: list
    alg_left: list
    alg_right: list
    kind: str = "H5"

    def bv_term(self):
        return self.bv

    def poly_term(self, enc):
        return E.eqP(self.alg_left, self.alg_right)

    def __str__(self):
        l, r = self.left, self.right
        return (f"{self.kind}: {l['src'].name} - {l['low'].name} = "
                f"{r['src'].name} - {r['low'].name}")


def drop_claim(left: dict, right: dict, enc):
    """The bit-vector claim alone — cheap, and it is what z3 is asked to prove."""
    n = max(left["src"].width, right["src"].width) + 1
    return ["=", _drop_bv(left, n, enc), _drop_bv(right, n, enc)]


def make_drop_hint(left: dict, right: dict, enc, claim) -> DropHint:
    """Only called once the claim is proved: building the algebraic terms asks the
    encoder for atoms, and an atom in a reading the segment did not already use adds
    an alias and a bridge — new unknowns the solver would then have to carry."""
    return DropHint(left, right, claim, _drop_alg(left, enc), _drop_alg(right, enc))


def _ext(v, n: int, enc):
    """v widened to n bits the way its own signedness reads it."""
    term = enc.bv(v)
    if n == v.width:
        return term
    kind = "sign_extend" if v.signed else "zero_extend"
    return E.extend(kind, n - v.width, term)


def _drop_bv(split: dict, n: int, enc):
    """The dropped amount as a bit-vector, computed wide enough not to wrap."""
    return ["bvsub", _ext(split["src"], n, enc), _ext(split["low"], n, enc)]


def _drop_alg(split: dict, enc):
    return E.PSub(E.PConst(enc.atom(split["src"])), E.PConst(enc.atom(split["low"])))


MAX_DECOMP_BITS = 12


@dataclass
class DecompHint:
    """H6: ⟦v⟧ = Σ 2ⁱ·⟦bᵢ⟧, where each bᵢ is a one-bit symbol z3 showed to be bit i
    of v, and v's bits above the last one are provably zero.

    `atom` is the *unsigned* reading: the decomposition itself proves v is below 2^m,
    so the two readings agree, and the unsigned one is the atom the split equations
    around it already use — the signed alias would make the solver chase the bridge."""
    value: object
    bits: list                 # [(i, symbol name)], i ascending from 0
    atom: object = None
    kind: str = "H6"

    def bv_term(self):
        w = self.value.width
        terms = [["bvshl", E.extend("zero_extend", w - 1, name), E.bv_const(i, w)]
                 if i else E.extend("zero_extend", w - 1, name)
                 for i, name in self.bits]
        return ["=", self.value.name, _sum_bv(terms)]

    def poly_term(self, enc):
        total = None
        for i, name in self.bits:
            term = E.PConst(enc.atom_of(name, 1))
            if i:
                term = E.PMul(term, E.PInt(1 << i))
            total = term if total is None else E.PAdd(total, term)
        return E.eqP(E.PConst(self.atom), total)

    def __str__(self):
        return (f"{self.kind}: {self.value.name} = "
                + " + ".join(f"2^{i}*{n}" if i else n for i, n in self.bits))


def _sum_bv(terms):
    out = terms[0]
    for t in terms[1:]:
        out = ["bvadd", out, t]
    return out


def decompositions(vc, sim: "Samples", prove, fixed: set | None = None,
                   limit: int = 600) -> list:
    """H6 candidates.

    Two passes. The first takes apart the values the segment itself shifted or masked,
    bit by bit — that is the shift-and-add multiplier. The second looks for a value that
    simply *is* a one-bit symbol, which is what `!(!x)` on a value the precondition keeps
    below 2 compiles to.

    Symbols already pinned to a constant are skipped — they match any bit that happens
    to be zero and would pad the equation with useless terms — and a chain stops at the
    first bit above which the value is provably zero, which keeps the decomposition
    minimal. Every claim either pass needs is filtered on the samples and then proved in
    one batch; the chains are put together from the answers afterwards.

    Each pass asks at most `limit` claims, narrowest values first: the booleans worth
    finding are C's `_Bool`-sized results of `!(!x)`, while a 128-bit sum that happens to
    be 0 or 1 is already tied to its carry by an exact narrowing. On a 4-limb Montgomery
    multiplication the second pass otherwise asks 1307 claims (14 minutes) to keep four
    hints.
    """
    fixed = fixed or set()
    ones = sorted(n for n, s in vc.seg.decls.items()
                  if isinstance(s, list) and s[:2] == ["_", "BitVec"] and int(s[2]) == 1
                  and n not in fixed)
    found, seen = [], set()

    # pass 1: claims for every shifted value, then the chains
    plans, claims = [], []

    def ask(claim) -> int | None:
        if len(claims) >= limit:
            return None
        claims.append(claim)
        return len(claims) - 1

    for v in sorted(dict.fromkeys(vc.seg.shifted), key=lambda v: v.width):
        if v.name in seen or v.name in vc.enc.consts or v.name not in vc.seg.decls:
            continue
        seen.add(v.name)
        w, top = v.width, min(v.width, MAX_DECOMP_BITS)
        above = {i: ask(["=", E.extract(w - 1, i, v.name), E.bv_const(0, w - i)])
                 for i in range(1, top + 1) if i < w and sim.high_zero(v.name, w, i)}
        bits = {i: [(b, ask(["=", b, E.extract(i, i, v.name)]))
                    for b in sim.bit_matches(ones, v.name, i)] for i in range(top)}
        plans.append((v, above, bits))
    proved = prove(claims)

    def ok(q) -> bool:
        return q is not None and proved[q]

    for v, above, bits in plans:
        w, top = v.width, min(v.width, MAX_DECOMP_BITS)
        chain, done = {}, False
        for i in range(top):
            if i and i < w and ok(above.get(i)):
                done = True                 # nothing left above bit i-1
                break
            b = next((b for b, q in bits[i] if ok(q)), None)
            if b is None:
                break
            chain[i] = b
        m = len(chain)
        if m == 0:
            continue
        if not done and m < w and not ok(above.get(m)):
            continue                        # the bits above are not zero
        found.append(DecompHint(v, [(i, chain[i]) for i in range(m)]))

    # pass 2: values that are a single bit
    plans, claims = [], []
    for name, v in sorted(vc.seg.values.items(), key=lambda kv: (kv[1].width, kv[0])):
        if v.width == 1 or name in seen or name in vc.enc.consts or name in fixed:
            continue
        if not sim.boolean(name) or not sim.varies(name):
            continue
        boolean = ask(["=", E.extract(v.width - 1, 1, v.name), E.bv_const(0, v.width - 1)])
        pairs = [(b, ask(["=", v.name, E.extend("zero_extend", v.width - 1, b)]))
                 for b in ones if sim.same(name, b)]
        plans.append((v, boolean, pairs))
    proved = prove(claims)
    for v, boolean, pairs in plans:
        if not ok(boolean):
            continue                        # not a boolean; no point pairing it up
        b = next((b for b, q in pairs if ok(q)), None)
        if b is not None:
            found.append(DecompHint(v, [(0, b)]))

    return _finish(vc, found)


def _finish(vc, found: list) -> list:
    kept = _drop_redundant(found)
    for h in kept:                          # atoms only for the hints that survive
        h.atom = vc.enc.read(h.value, False)
    return kept


def _drop_redundant(found: list) -> list:
    """A shifted copy of a value decomposes into the same bits minus the low ones, and
    the shift's own split equation already says that, so the shorter decomposition adds
    nothing but work for the solver. Keep the longest chain, and one of any duplicates."""
    out = []
    for h in found:
        syms = [n for _, n in h.bits]
        if any(other is not h and _covers(syms, [n for _, n in other.bits], other in out)
               for other in found):
            continue
        out.append(h)
    return out


def _covers(short: list, long: list, kept: bool) -> bool:
    if len(short) < len(long):
        return long[len(long) - len(short):] == short
    return short == long and kept


def split_pairs(vc, sim: "Samples", limit: int = 24) -> list[tuple[dict, dict]]:
    """H5 candidates: SPLIT narrowings that keep the same number of bits and drop the
    same amount on every sample. Narrowings to different widths drop amounts on
    different scales and are never equal."""
    groups: dict = {}
    for i, a in enumerate(vc.seg.splits):
        groups.setdefault((a["width"], sim.drop(a)), []).append(i)
    out = []
    splits = vc.seg.splits
    for i, a in enumerate(splits):
        for j in groups[(a["width"], sim.drop(a))]:
            if j > i and len(out) < limit:
                out.append((a, splits[j]))
    return out


def candidates(vc) -> list[tuple[str, int, str]]:
    """(symbol, width, kind) worth testing, in emission order."""
    out: list[tuple[str, int, str]] = []
    widths = {n: int(s[2]) for n, s in vc.seg.decls.items()
              if isinstance(s, list) and s[:2] == ["_", "BitVec"]}
    for note in vc.seg.notes:
        for name in _witnesses(note):
            if name in widths:
                out.append((name, widths[name], "H1" if note["rule"] in
                            ("L7", "L9'", "L9m", "L11") else "H3"))
    for name, w in widths.items():
        if w == 1 and not any(name == c[0] for c in out):
            out.append((name, 1, "H3"))
    seen, uniq = set(), []
    for c in out:
        if c[0] not in seen:
            seen.add(c[0])
            uniq.append(c)
    return uniq


def _witnesses(note: dict) -> list[str]:
    w = note.get("witness")
    if not w:
        return []
    return [w] if isinstance(w, str) else list(w)


def discover(vc, z3_bin: str = "z3", timeout: float = 10.0, max_pairs: int = 60,
             samples: list | None = None, jobs: int | None = None) -> list:
    """Prove candidates on this segment's range model.

    `samples` are the segment's symbols evaluated on real runs (sample_envs). A
    candidate that is false on one of them cannot be proved, so it never reaches z3;
    the rest are sliced and proved in batches (vc/prover.py). Without samples every
    candidate goes to z3, as before."""
    found: list = []
    model = prover.RangeModel(vc.seg, vc.premise_range)
    sim = Samples(vc, samples)

    def prove(claims):
        return prover.prove_all(model, claims, z3_bin, timeout, jobs)

    # H1–H3: a symbol equal to a constant; the first value proved wins
    fixed: set[str] = set()
    tries = []
    for name, width, kind in candidates(vc):
        options = [(v, kind) for v in ((0,) if width > 1 else (0, 1))]
        if width > 1:
            options.append(((1 << width) - 1, "H2"))
        tries += [(name, width, v, k) for v, k in options if sim.constant(name, v)]
    proved = prove([["=", n, E.bv_const(v, w)] for n, w, v, _ in tries])
    for (name, width, value, kind), ok in zip(tries, proved):
        if ok and name not in fixed:
            found.append(Hint(name, width, value, kind))
            fixed.add(name)
    # H4: pairs of 1-bit symbols that always agree. Symbols already pinned to a constant
    # need no pairing, and only 1-bit symbols are worth the solver calls.
    ones = sorted(n for n, s in vc.seg.decls.items()
                  if isinstance(s, list) and s[:2] == ["_", "BitVec"] and int(s[2]) == 1
                  and n not in fixed)
    groups: dict = {}
    for n in ones:
        groups.setdefault(sim.signature(n), []).append(n)
    pairs = []
    for i, a in enumerate(ones):
        for b in groups[sim.signature(a)]:
            if b > a and len(pairs) < max_pairs:
                pairs.append((a, b))
    for (a, b), ok in zip(pairs, prove([["=", a, b] for a, b in pairs])):
        if ok:
            found.append(PairHint(a, b, 1))
    # H5: two SPLIT narrowings that drop the same amount.
    pairs = split_pairs(vc, sim)
    claims = [drop_claim(left, right, vc.enc) for left, right in pairs]
    for (left, right), claim, ok in zip(pairs, claims, prove(claims)):
        if ok:
            found.append(make_drop_hint(left, right, vc.enc, claim))
    # H6: a value put back together from the bits the segment read out of it.
    found += decompositions(vc, sim, prove, fixed)
    for h in found:                         # the slice each hint was proved on (§7.4)
        h.depth = _depth(h, model)
    return found


def _depth(h, model):
    """The cone depth that proved the hint, None for the full cone. A decomposition was
    proved bit by bit; the deepest of those slices holds all of them."""
    if isinstance(h, DecompHint):
        w = h.value.width
        claims = [["=", b, E.extract(i, i, h.value.name)] for i, b in h.bits]
        m = len(h.bits)
        if m < w:
            claims.append(["=", E.extract(w - 1, m, h.value.name), E.bv_const(0, w - m)])
        got = [model.depth_of.get(to_str(c), None) for c in claims]
        known = [d for d, c in zip(got, claims) if to_str(c) in model.depth_of]
        if len(known) < len(claims) or any(d is None for d in known):
            return None
        return max(known)
    return model.depth_of.get(to_str(h.bv_term()))


# ------------------------------------------------------------------- samples
class Samples:
    """The segment's symbols on real runs, used to throw out candidates that some run
    already refutes. With no samples every question answers "maybe", so every
    candidate goes to the solver."""

    def __init__(self, vc, envs: list | None):
        self.envs = envs or []
        self.consts = vc.enc.consts
        self._cache: dict[str, tuple | None] = {}
        self._by_sig: dict | None = None

    def _values(self, name: str):
        if name in self._cache:
            return self._cache[name]
        got = None
        if self.envs and name not in self.consts:
            try:
                got = tuple(env.bv[name] for env in self.envs)
            except KeyError:
                got = None
        self._cache[name] = got
        return got

    def signature(self, name: str):
        """Equal signatures are necessary for equal symbols; None matches nothing but
        itself, so an unknown symbol is grouped with the other unknowns."""
        return self._values(name)

    def constant(self, name: str, value: int) -> bool:
        vals = self._values(name)
        return vals is None or all(x == value for x in vals)

    def same(self, a: str, b: str) -> bool:
        va, vb = self._values(a), self._values(b)
        return va is None or vb is None or va == vb

    def boolean(self, name: str) -> bool:
        vals = self._values(name)
        return vals is None or all(x in (0, 1) for x in vals)

    def high_zero(self, name: str, width: int, i: int) -> bool:
        vals = self._values(name)
        return vals is None or all(x >> i == 0 for x in vals)

    def varies(self, name: str, i: int | None = None) -> bool:
        """Does `name` (or its bit i) take more than one value over the samples? A
        constant signature matches every other constant one, so it says nothing about
        which symbol a bit is; with no samples the answer is "maybe"."""
        vals = self._values(name)
        if vals is None:
            return True
        if i is not None:
            vals = tuple((y >> i) & 1 for y in vals)
        return len(set(vals)) > 1

    def bit_matches(self, ones: list[str], name: str, i: int) -> list[str]:
        """The one-bit symbols (in the given order) that agree with bit i of `name` on
        every sample — looked up by signature, not compared one by one. A bit that is
        the same on every sample matches nothing: see varies()."""
        vals = self._values(name)
        if vals is None:
            return list(ones)
        if not self.varies(name, i):
            return []
        if self._by_sig is None or self._by_sig[0] is not ones:
            index: dict = {}
            unknown = []
            for b in ones:
                sig = self._values(b)
                (unknown if sig is None else index.setdefault(sig, [])).append(b)
            self._by_sig = (ones, index, unknown)
        _, index, unknown = self._by_sig
        want = tuple((y >> i) & 1 for y in vals)
        hits = set(index.get(want, [])) | set(unknown)
        return [b for b in ones if b in hits] if unknown else index.get(want, [])

    def drop(self, split: dict):
        """⟦src⟧ − ⟦low⟧ on each sample, or None when a side is not a symbol here."""
        if not self.envs:
            return None
        out = []
        for env in self.envs:
            got = []
            for v in (split["src"], split["low"]):
                if v.name in self.consts:
                    pattern = self.consts[v.name] & ((1 << v.width) - 1)
                elif v.name in env.bv:
                    pattern = env.bv[v.name]
                else:
                    return None
                got.append(interpret(pattern, v.width, v.signed))
            out.append(got[0] - got[1])
        return tuple(out)


def sample_runs(trace, target, n: int, seed: int = 11) -> list | None:
    """Value patterns of n runs that satisfy the precondition, or None if the sampler
    cannot find such inputs (then nothing is filtered)."""
    if n <= 0:
        return None
    from ..gates import runs
    try:
        return [patterns for _, patterns in runs(trace, target, n, seed=seed, edges=True)]
    except RuntimeError:
        return None


def sample_envs(vc, runs: list | None) -> list | None:
    """The segment's symbols — program values, then witnesses and bridges from their
    defining statements — on each run."""
    if not runs:
        return None
    widths = evaluate.widths_of(vc.seg)
    out = []
    try:
        for patterns in runs:
            env = evaluate.Env({k: v for k, v in patterns.items() if k in widths}, widths)
            out.append(evaluate.solve_definitions(vc.seg, env))
    except evaluate.EvalError:
        return None
    return out
