"""Integer encoding and term construction for the two models (spec §6.1, D4).

⟦v⟧ is the integer a bit-vector stands for. Unsigned values read as `(bv2nat v)`.
Signed values read as an Int alias `s__v` defined by two's complement (D4), or, with
--int-encoding=bv2int, as `(bv2int v)` — that one is only sound for unsigned values
(F3) and exists to A/B against the golden files.

Both readings of the same value are atoms (M5); when a value is read in the
signedness it was not declared with, the L10 bridge relates the two atoms.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from ..ir.interp import interpret
from ..ir.ops import Value

ALIAS = "alias"
BV2INT = "bv2int"


def bv_const(value: int, width: int) -> str:
    """M8: #x when the width is a multiple of 4, else #b."""
    v = value & ((1 << width) - 1)
    if width % 4 == 0:
        return "#x" + format(v, f"0{width // 4}X")
    return "#b" + format(v, f"0{width}b")


def int_const(n: int):
    """M8: Int literals are decimal; negatives are (- n)."""
    return ["-", str(-n)] if n < 0 else str(n)


def bv_sort(width: int):
    return ["_", "BitVec", str(width)]


def extend(kind: str, by: int, term):
    return [["_", kind, str(by)], term]


def extract(hi: int, lo: int, term):
    return [["_", "extract", str(hi), str(lo)], term]


# ---------------------------------------------------------------- Poly terms
def PConst(atom):
    return ["PConst", atom]


def PInt(n: int):
    return ["PConst", int_const(n)]


def PAdd(a, b):
    return ["PAdd", a, b]


def PSub(a, b):
    return ["PSub", a, b]


def PMul(a, b):
    return ["PMul", a, b]


def PNeg(a):
    return ["PNeg", a]


def PPow(a, k: int):
    return ["PPow", a, str(k)]


def eqP(a, b):
    return ["eqP", a, b]


def psum(terms):
    it = iter(terms)
    out = next(it)
    for t in it:
        out = PAdd(out, t)
    return out


@dataclass
class Segment:
    """One segment's two models plus its obligations (spec §7.1)."""
    decls: dict[str, list] = field(default_factory=dict)     # name -> sort
    bv: list = field(default_factory=list)                   # range-section terms
    alg: list = field(default_factory=list)                  # algebraic-section terms
    safety: list = field(default_factory=list)               # QF_BV obligations
    notes: list = field(default_factory=list)                # (instr index, rule, decision)
    bridge_alg: set = field(default_factory=set)             # indices of L10 bridges in alg
    splits: list = field(default_factory=list)               # SPLIT narrowings, for H5
    shifted: list = field(default_factory=list)              # values taken apart, for H6
    values: dict = field(default_factory=dict)               # name -> Value, for H6
    alias_eqs: list = field(default_factory=list)            # (value, reading, atom): copies
    split_at: dict = field(default_factory=dict)             # (value, k) -> L9m (high, low)

    def declare(self, name: str, sort) -> None:
        if name in self.decls and self.decls[name] != sort:
            raise ValueError(f"{name} declared with two sorts")
        self.decls[name] = sort


class Encoder:
    def __init__(self, segment: Segment, mode: str = ALIAS, intervals: dict | None = None,
                 defined_signed: dict | None = None, copy_alias: bool = False):
        if mode not in (ALIAS, BV2INT):
            raise ValueError(mode)
        self.seg = segment
        self.mode = mode
        self.intervals = intervals or {}
        # How each value was *defined*. An interval is a statement about that reading;
        # the same bits relabelled the other way stand for different integers, so the
        # two must not be mixed up.
        self.defined_signed = defined_signed or {}
        self.consts: dict[str, int] = {}     # L1: constants are inlined, never declared
        self._bridged: set[str] = set()
        self._readings: dict[str, set] = {}
        self._aliased: set[str] = set()
        self._witnesses = 0
        # Copies (L8, EXACT L9) reuse the atom of what they copy instead of getting
        # their own and an equation saying the two are equal (§6.3): (name, reading)
        # -> that atom. Half of an NTT layer's algebraic statements were such copies.
        self.copy_alias = copy_alias
        self._alias: dict[tuple[str, bool], object] = {}

    # ------------------------------------------------------------ symbols
    def declare(self, v: Value) -> None:
        if v.name not in self.consts:
            self.seg.declare(v.name, bv_sort(v.width))
            self.seg.values.setdefault(v.name, v)

    def set_const(self, v: Value, value: int) -> None:
        self.consts[v.name] = value

    def bv(self, v: Value):
        """The bit-vector term for v: the literal for a constant (L1), else its name."""
        if v.name in self.consts:
            return bv_const(self.consts[v.name], v.width)
        self.declare(v)
        return v.name

    def witness(self, kind: str, width: int, signed: bool) -> Value:
        """M7: witness names are w<kind><n>."""
        v = Value(f"w{kind}{self._witnesses}", width, signed, "witness")
        self._witnesses += 1
        self.declare(v)
        return v

    # ------------------------------------------------------------ readings
    def atom(self, v: Value, signed: bool | None = None):
        """An Int atom for ⟦v⟧ in the requested signedness (default: the value's own).

        Whichever way a caller arrives at the two readings of one value — asking for
        both here, or two rules each asking for the one they need — the second of them
        emits the L10 bridge. Nothing else relates `(bv2nat v)` to `s__v`, so leaving it
        out would silently split the value in two as far as the algebraic model is
        concerned, and the proof would be missing a step it looks like it has."""
        signed = v.signed if signed is None else signed
        if (v.name, signed) in self._alias:
            return self._alias[(v.name, signed)]
        if v.name in self.consts:
            pattern = self.consts[v.name] & ((1 << v.width) - 1)
            return int_const(interpret(pattern, v.width, signed))
        term = self._atom_term(v, signed)
        self._note_reading(v, signed)
        return term

    def _atom_term(self, v: Value, signed: bool):
        self.declare(v)
        if not signed:
            return ["bv2nat", v.name]
        if self.mode == BV2INT:
            return ["bv2int", v.name]
        name = f"s__{v.name}"
        if name not in self._aliased:
            self._aliased.add(name)
            self.seg.declare(name, "Int")
            self.seg.bv.append(["=", name, self._twos_complement(v)])
        return name

    def alias(self, v: Value, signed: bool, target) -> None:
        """⟦v⟧ read `signed` is the integer the atom `target` already stands for: from
        now on that atom is v's too, and no equation is emitted. The identity is kept in
        seg.alias_eqs, where the rule lemmas (A1.1) and G3 check it like any statement."""
        self._alias[(v.name, signed)] = target
        self.seg.alias_eqs.append((v, signed, target))
        self._note_reading(v, signed)

    def alias_statements(self) -> list:
        """The identities the aliases stand for, as algebraic statements — for the rule
        lemmas, which have to prove them; a VC never states them."""
        return [eqP(PConst(self._atom_term(v, signed)), PConst(target))
                for v, signed, target in self.seg.alias_eqs]

    def _resolved(self, v: Value, signed: bool):
        return self._alias.get((v.name, signed)) or self._atom_term(v, signed)

    def atom_of(self, name: str, width: int, signed: bool = False):
        """An atom for a symbol known only by name (hints): its alias if it has one."""
        if (name, signed) in self._alias:
            return self._alias[(name, signed)]
        return ["bv2nat", name] if not signed else f"s__{name}"

    def _note_reading(self, v: Value, signed: bool) -> None:
        seen = self._readings.setdefault(v.name, set())
        seen.add(signed)
        if len(seen) == 2:
            self._bridge(v)

    def _bridge(self, v: Value) -> None:
        """L10: ⟦v⟧ᵤ = ⟦v⟧ₛ + 2^w·⟦b⟧, with b the sign bit, defined in the range model.

        When the interval analysis already knows the sign bit, the witness is replaced
        by the constant and the range VC gets the obligation to prove it — the same
        bargain as an EXACT decision (§6.2). A witness that the solver has to carry
        around costs far more than the equation is worth: every extra unknown widens
        the Gröbner computation, and these appear once per value."""
        if v.name in self._bridged:
            return
        self._bridged.add(v.name)
        u, s = self._resolved(v, False), self._resolved(v, True)
        bit = self._known_sign_bit(v)
        self.seg.bridge_alg.add(len(self.seg.alg))
        if bit is None:
            b = self.witness("b", 1, False)
            self.seg.bv.append(["=", b.name, extract(v.width - 1, v.width - 1, v.name)])
            self.seg.alg.append(eqP(PAdd(PConst(s), PMul(PConst(self._atom_term(b, False)),
                                                         PInt(1 << v.width))), PConst(u)))
            return
        self.seg.safety.append(["=", extract(v.width - 1, v.width - 1, v.name),
                                "#b1" if bit else "#b0"])
        self.seg.alg.append(eqP(PConst(s), PConst(u)) if not bit else
                            eqP(PAdd(PConst(s), PInt(1 << v.width)), PConst(u)))

    def _known_sign_bit(self, v: Value) -> int | None:
        """The top bit of v's bit pattern, when the interval analysis already fixes it."""
        span = self.intervals.get(v.name)
        if span is None:
            return None
        half = 1 << (v.width - 1)
        if self.defined_signed.get(v.name, v.signed):
            if 0 <= span.lo and span.hi < half:
                return 0
            return 1 if -half <= span.lo and span.hi < 0 else None
        return 0 if span.hi < half else (1 if span.lo >= half else None)

    def _twos_complement(self, v: Value):
        w = v.width
        return ["-", ["bv2nat", v.name],
                ["*", str(1 << w), ["bv2nat", extract(w - 1, w - 1, v.name)]]]

    def both(self, v: Value):
        """Atoms for (unsigned, signed) readings of v; the bridge comes with them."""
        return self.atom(v, signed=False), self.atom(v, signed=True)

    def read(self, v: Value, signed: bool):
        """⟦v⟧ in `signed`, bridging when that is not how v is declared."""
        return self.atom(v, signed)
