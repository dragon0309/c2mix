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
plus the range premises. Soundness does not rest on that proof alone: the range VC
re-proves every emitted hint (G5), and dropping a hint can only make the algebraic
proof harder, never unsound.
"""
from __future__ import annotations

import subprocess
from dataclasses import dataclass

from ..lower import encode as E
from ..mixfmt.writer import to_str


def _reading(seg, name: str, width: int):
    """(atom, is the reading signed) for a symbol, following how it is read elsewhere."""
    if f"s__{name}" in seg.decls:
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
        atom, signed = _reading(enc.seg, self.symbol, self.width)
        value = -self.value if signed and self.width == 1 else self.value
        return E.eqP(E.PConst(atom), E.PInt(value))

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
        la, ls = _reading(enc.seg, self.left, self.width)
        ra, rs = _reading(enc.seg, self.right, self.width)
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
            term = E.PConst(["bv2nat", name])
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


def decompositions(vc, base, z3_bin: str, timeout: float, fixed: set | None = None,
                   budget: int = 160) -> list:
    """H6 candidates.

    Two passes. The first takes apart the values the segment itself shifted or masked,
    bit by bit — that is the shift-and-add multiplier. The second looks for a value that
    simply *is* a one-bit symbol, which is what `!(!x)` on a value the precondition keeps
    below 2 compiles to; it is filtered by one solver call per value, so it stays cheap
    even with many values in scope.

    Symbols already pinned to a constant are skipped — they match any bit that happens
    to be zero and would pad the equation with useless terms — and the bit search stops
    as soon as the bits above are provably zero, which keeps the decomposition minimal.
    """
    fixed = fixed or set()
    ones = sorted(n for n, s in vc.seg.decls.items()
                  if isinstance(s, list) and s[:2] == ["_", "BitVec"] and int(s[2]) == 1
                  and n not in fixed)
    found, seen = [], set()
    spent = [0]

    def prove(claim) -> bool:
        if spent[0] >= budget:
            return False
        spent[0] += 1
        return _proves(base, claim, z3_bin, timeout)

    for v in vc.seg.shifted:
        if v.name in seen or v.name in vc.enc.consts or v.name not in vc.seg.decls:
            continue
        seen.add(v.name)
        bits, w, done = {}, v.width, False
        for i in range(min(w, MAX_DECOMP_BITS)):
            if i and i < w and prove(["=", E.extract(w - 1, i, v.name),
                                      E.bv_const(0, w - i)]):
                done = True                 # nothing left above bit i-1
                break
            for b in ones:
                if prove(["=", b, E.extract(i, i, v.name)]):
                    bits[i] = b
                    break
            if i not in bits:
                break
        m = 0
        while m in bits:
            m += 1
        if m == 0:
            continue
        if not done and m < w and not prove(["=", E.extract(w - 1, m, v.name),
                                             E.bv_const(0, w - m)]):
            continue                        # the bits above are not zero
        found.append(DecompHint(v, [(i, bits[i]) for i in range(m)]))

    spent[0] = 0                            # the second pass gets its own budget
    for name, v in sorted(vc.seg.values.items()):
        if v.width == 1 or name in seen or name in vc.enc.consts or name in fixed:
            continue
        if not prove(["=", E.extract(v.width - 1, 1, v.name), E.bv_const(0, v.width - 1)]):
            continue                        # not a boolean; no point pairing it up
        for b in ones:
            if prove(["=", v.name, E.extend("zero_extend", v.width - 1, b)]):
                found.append(DecompHint(v, [(0, b)]))
                break

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


def split_pairs(vc, limit: int = 24) -> list[tuple[dict, dict]]:
    """H5 candidates: SPLIT narrowings that keep the same number of bits. Narrowings
    to different widths drop amounts on different scales and are never equal."""
    out = []
    splits = vc.seg.splits
    for i, a in enumerate(splits):
        for b in splits[i + 1:]:
            if a["width"] == b["width"] and len(out) < limit:
                out.append((a, b))
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


def discover(vc, z3_bin: str = "z3", timeout: float = 10.0, max_pairs: int = 60) -> list:
    """Prove candidates one at a time on this segment's range model."""
    found: list = []
    base = _range_model(vc)
    fixed: set[str] = set()
    for name, width, kind in candidates(vc):
        for value in (0,) if width > 1 else (0, 1):
            if _proves(base, ["=", name, E.bv_const(value, width)], z3_bin, timeout):
                found.append(Hint(name, width, value, kind))
                fixed.add(name)
                break
        else:
            if width > 1 and _proves(base, ["=", name, E.bv_const((1 << width) - 1, width)],
                                     z3_bin, timeout):
                found.append(Hint(name, width, (1 << width) - 1, "H2"))
                fixed.add(name)
    # H4: pairs of 1-bit symbols that always agree. Symbols already pinned to a constant
    # need no pairing, and only 1-bit symbols are worth the solver calls.
    ones = [n for n, s in vc.seg.decls.items()
            if isinstance(s, list) and s[:2] == ["_", "BitVec"] and int(s[2]) == 1
            and n not in fixed]
    calls = 0
    for i, a in enumerate(sorted(ones)):
        for b in sorted(ones)[i + 1:]:
            if calls >= max_pairs:
                break
            calls += 1
            if _proves(base, ["=", a, b], z3_bin, timeout):
                found.append(PairHint(a, b, 1))
    # H5: two SPLIT narrowings that drop the same amount.
    for left, right in split_pairs(vc):
        claim = drop_claim(left, right, vc.enc)
        if _proves(base, claim, z3_bin, timeout):
            found.append(make_drop_hint(left, right, vc.enc, claim))
    # H6: a value put back together from the bits the segment read out of it.
    found += decompositions(vc, base, z3_bin, timeout, fixed)
    return found


def _range_model(vc) -> list[str]:
    lines = ["(set-logic QF_BV)"]
    for n, sort in vc.seg.decls.items():
        if isinstance(sort, list) and sort[:2] == ["_", "BitVec"]:
            lines.append(to_str(["declare-const", n, sort]))
    for t in vc.premise_range:
        lines.append(to_str(["assert", t]))
    for t in vc.seg.bv:
        if isinstance(t, list) and t[0] == "=" and isinstance(t[1], str) \
                and t[1] not in vc.seg.decls:
            continue
        if isinstance(t, list) and t[0] == "=" and vc.seg.decls.get(t[1]) == "Int":
            continue                       # Int alias definitions are not part of this model
        lines.append(to_str(["assert", t]))
    return lines


def _proves(base: list[str], claim, z3_bin: str, timeout: float) -> bool:
    script = "\n".join(base + [to_str(["assert", ["not", claim]]), "(check-sat)"]) + "\n"
    try:
        p = subprocess.run([z3_bin, "-in", "-smt2"], input=script,
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return False
    out = p.stdout.strip().splitlines()
    return bool(out) and out[-1].strip() == "unsat" and "(error" not in p.stdout
