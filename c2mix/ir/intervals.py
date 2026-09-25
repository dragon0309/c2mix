"""Interval analysis and the EXACT/SPLIT decision (spec §6.2, D6).

Intervals are over the *interpreted* integer of a value (signed where its
signedness says so), not over bit patterns. Forward propagation only: the start of
a segment is the range precondition, everything else follows from the operations.

An operation that can overflow is EXACT when its exact result provably fits the
result type — then lowering writes a precise algebraic equation and a safety
obligation for the range VC. Otherwise it is SPLIT: the value is computed at a
wider width and split into high and low parts. Both are sound; SPLIT is just weaker.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from .ops import Instr, Program, Value

EXACT = "EXACT"
SPLIT = "SPLIT"
FREE = "FREE"           # L13: no algebraic statement at all
OVERFLOWING = {"add", "sub", "neg", "mul", "shl"}


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError(f"empty interval [{self.lo}, {self.hi}]")

    def __contains__(self, x: int) -> bool:
        return self.lo <= x <= self.hi

    def fits(self, v: Value) -> bool:
        return v.lo <= self.lo and self.hi <= v.hi

    def hull(self, o: "Interval") -> "Interval":
        return Interval(min(self.lo, o.lo), max(self.hi, o.hi))

    def __add__(self, o): return Interval(self.lo + o.lo, self.hi + o.hi)
    def __sub__(self, o): return Interval(self.lo - o.hi, self.hi - o.lo)
    def __neg__(self): return Interval(-self.hi, -self.lo)

    def __mul__(self, o):
        c = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return Interval(min(c), max(c))

    def shl(self, k: int) -> "Interval":
        return Interval(self.lo << k, self.hi << k)

    def floordiv_pow2(self, k: int) -> "Interval":
        return Interval(self.lo >> k, self.hi >> k)

    def __str__(self) -> str:
        return f"[{self.lo}, {self.hi}]"


def full(v: Value) -> Interval:
    return Interval(v.lo, v.hi)


@dataclass
class Analysis:
    intervals: dict[str, Interval]
    decisions: dict[int, str]           # index in prog.instrs -> EXACT/SPLIT/FREE
    consts: dict[str, int]
    masks: set = field(default_factory=set)
    """Values that hold either all zeros or all ones. Branch-free code selects with
    them (§6.3's mask form of L12), and the algebraic equation for that only holds
    when the mask really is one — so it is tracked here rather than assumed."""

    def of(self, v: Value) -> Interval:
        return self.intervals[v.name]


def analyze(prog: Program, pre: dict[str, Interval] | None = None,
            force_split: bool = False, span: tuple[int, int] | None = None,
            known: dict[str, Interval] | None = None) -> Analysis:
    """`pre` gives the range precondition per input name; inputs without one get
    the full range of their type. `force_split` is --exactness=split.

    `span` analyses one segment (§6.2): only instructions in [lo, hi) are visited, and
    `known` carries the intervals of values the earlier segments defined — that is the
    range precondition of this cut, everything else falling back to the full type."""
    pre = pre or {}
    iv: dict[str, Interval] = {}
    consts: dict[str, int] = {}
    for v in prog.inputs:
        got = pre.get(v.name, full(v))
        if not got.fits(v):
            raise ValueError(f"precondition {got} for {v} is outside its type")
        iv[v.name] = got
    lo, hi = span or (0, len(prog.instrs))
    for idx, ins in enumerate(prog.instrs):
        if ins.op == "const":                    # constants are global facts
            consts[ins.result.name] = ins.value
            iv[ins.result.name] = Interval(ins.value, ins.value)
        elif not lo <= idx < hi and ins.result is not None:
            v = ins.result
            iv[v.name] = (known or {}).get(v.name, full(v))
    decisions: dict[int, str] = {}
    widths = {ins.result.name: ins.result.width for ins in prog.instrs if ins.op == "const"}
    masks: set[str] = {n for n, c in consts.items()
                       if c == 0 or c == -1 or _all_ones(c, widths[n])}
    for idx, ins in enumerate(prog.instrs[lo:hi], start=lo):
        if ins.op == "marker":
            continue
        if ins.result is not None and _is_mask(ins, iv, masks):
            masks.add(ins.result.name)
        r = ins.result
        args = [iv[a.name] for a in ins.args]
        exact, unconstrained = _transfer(ins, args, consts)
        if ins.op in OVERFLOWING or (ins.op == "extract" and _is_narrowing(ins)):
            if exact is not None and exact.fits(r) and not force_split:
                decisions[idx] = EXACT
                iv[r.name] = exact
            else:
                decisions[idx] = SPLIT
                iv[r.name] = full(r)
        else:
            decisions[idx] = FREE if unconstrained else EXACT
            iv[r.name] = exact if exact is not None else full(r)
    return Analysis(iv, decisions, consts, masks)


def _all_ones(value: int, width: int) -> bool:
    return value & ((1 << width) - 1) == (1 << width) - 1


def _is_mask(ins: Instr, iv: dict, masks: set) -> bool:
    """All zeros or all ones, propagated forward.

    `neg` of a 0/1 value and `sext` of a single bit are how C spells "broadcast this
    condition across the word"; after that, complement, bitwise combination with
    another mask, sign extension and taking a low field all preserve the shape.
    `zext` does not: zero-extending 0xFF gives 0x000000FF, which selects nothing."""
    op, args = ins.op, ins.args
    names = [a.name for a in args]
    if op == "neg":
        span = iv.get(names[0])
        return span is not None and span.lo >= 0 and span.hi <= 1
    if op == "sext":
        return args[0].width == 1 or names[0] in masks
    if op == "not":
        return names[0] in masks
    if op in ("and", "or", "xor"):
        return all(n in masks for n in names)
    if op == "extract":
        return ins.lo == 0 and names[0] in masks
    if op == "ite":
        return names[1] in masks and names[2] in masks
    return False


def _is_narrowing(ins: Instr) -> bool:
    """A low-field extract can lose information; other extracts are pure splits."""
    return ins.lo == 0 and ins.result.width < ins.args[0].width


def _transfer(ins: Instr, args: list[Interval], consts: dict[str, int]):
    """(exact interval of the mathematical result, is it algebraically free?)"""
    op, r = ins.op, ins.result
    if op == "const":
        return Interval(ins.value, ins.value), False
    if op == "add":
        return args[0] + args[1], False
    if op == "sub":
        return args[0] - args[1], False
    if op == "neg":
        return -args[0], False
    if op == "mul":
        return args[0] * args[1], False
    if op == "shl":
        return args[0].shl(ins.k), False
    if op in ("ashr", "lshr"):
        return args[0].floordiv_pow2(ins.k), False
    if op in ("sext", "zext"):
        return args[0], False
    if op == "extract":
        if _is_narrowing(ins):
            # value-preserving exactly when it fits, which gates the EXACT decision
            return args[0], False
        if ins.lo == 0 and r.width == ins.args[0].width:
            # same bits; if the reading changes, the range they stand for changes too
            return (args[0] if r.signed == ins.args[0].signed else full(r)), False
        return full(r), False                 # high/middle field: value is a split part
    if op == "not":
        return Interval(-1 - args[0].hi, -1 - args[0].lo) if ins.args[0].signed \
            else Interval((1 << r.width) - 1 - args[0].hi, (1 << r.width) - 1 - args[0].lo), False
    if op == "and":
        m = _mask_width(ins, consts)
        if m is not None:
            return Interval(0, (1 << m) - 1), False
        return full(r), True
    if op in ("or", "xor"):
        return full(r), True
    if op == "cmp":
        return Interval(0, 1), False
    if op == "ite":
        return args[1].hull(args[2]), False
    raise ValueError(f"no transfer function for {op}")


def mask_site(ins: Instr, consts: dict[str, int]) -> tuple[int, int] | None:
    """L9m: r = x & (2^k - 1), a mask that keeps the low k bits.
    Returns (k, index of the mask operand) — with two constant operands the mask is
    whichever one has that shape, not simply the first."""
    if ins.op != "and":
        return None
    for i in (0, 1):
        c = consts.get(ins.args[i].name)
        other = ins.args[1 - i]
        if c is None:
            continue
        c &= (1 << ins.args[i].width) - 1           # bit pattern of the constant
        k = c.bit_length()
        if c and c == (1 << k) - 1 and k < other.width:
            return k, i
    return None


def mask_width(ins: Instr, consts: dict[str, int]) -> int | None:
    got = mask_site(ins, consts)
    return got[0] if got else None


def _mask_width(ins: Instr, consts: dict[str, int]) -> int | None:
    return mask_width(ins, consts)


def check_containment(prog: Program, analysis: Analysis, env: dict[str, int]) -> list[str]:
    """A1.4: every concrete value must lie in its analyzed interval."""
    from .interp import interpret
    bad = []
    for v in prog.values():
        if v.name not in env:
            continue
        x = interpret(env[v.name], v.width, v.signed)
        got = analysis.intervals[v.name]
        if x not in got:
            bad.append(f"{v} = {x} outside {got}")
    return bad
