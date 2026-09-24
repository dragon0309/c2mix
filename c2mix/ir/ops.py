"""c2mix IR (spec §5.1, §5.2).

A trace is straight-line SSA over bit-vectors. Every value carries a width and a
signedness; the signedness is only an *interpretation* (§5.1), the bit-vector
itself has none. Control flow is already resolved by the executor, so the only
ordering construct left is `marker`, which separates segments.
"""
from __future__ import annotations

from dataclasses import dataclass, field, replace

MAX_WIDTH = 128

# op -> number of value arguments
BINARY = {"add", "sub", "mul", "and", "or", "xor"}
UNARY = {"neg", "not"}
SHIFTS = {"shl", "ashr", "lshr"}
CASTS = {"sext", "zext"}
CMP_PREDS = {"eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"}
SIGNED_PREDS = {"slt", "sle", "sgt", "sge"}


class IRError(Exception):
    pass


@dataclass(frozen=True)
class Value:
    name: str
    width: int
    signed: bool
    kind: str = "temp"          # input | temp | witness | alias | const
    loc: str | None = None      # source location, filled in from phase 3 on

    def __post_init__(self):
        if not 1 <= self.width <= MAX_WIDTH:
            raise IRError(f"{self.name}: width {self.width} outside [1, {MAX_WIDTH}]")

    def as_signed(self, signed: bool) -> "Value":
        return self if signed == self.signed else replace(self, signed=signed)

    @property
    def lo(self) -> int:
        return -(1 << (self.width - 1)) if self.signed else 0

    @property
    def hi(self) -> int:
        return (1 << (self.width - 1)) - 1 if self.signed else (1 << self.width) - 1

    def __str__(self) -> str:
        return f"{self.name}:{'i' if self.signed else 'u'}{self.width}"


@dataclass(frozen=True)
class Instr:
    op: str
    result: Value | None
    args: tuple = ()
    k: int | None = None        # shift amount / cast target width
    hi: int | None = None       # extract
    lo: int | None = None
    pred: str | None = None     # cmp
    value: int | None = None    # const (as the interpreted integer)
    tag: str | None = None      # marker

    def __str__(self) -> str:
        extra = "".join(f" {n}={v}" for n, v in
                        (("k", self.k), ("hi", self.hi), ("lo", self.lo),
                         ("pred", self.pred), ("value", self.value), ("tag", self.tag))
                        if v is not None)
        args = " ".join(str(a) for a in self.args)
        return f"{self.result or '-'} = {self.op} {args}{extra}".strip()


@dataclass
class Program:
    inputs: list[Value] = field(default_factory=list)
    instrs: list[Instr] = field(default_factory=list)

    def values(self):
        yield from self.inputs
        for i in self.instrs:
            if i.result is not None:
                yield i.result

    def __str__(self) -> str:
        return "\n".join(["inputs: " + ", ".join(str(v) for v in self.inputs)]
                         + [str(i) for i in self.instrs])


def check(prog: Program) -> None:
    """Well-formedness: SSA, operands defined before use, widths agree."""
    seen: dict[str, Value] = {}
    for v in prog.inputs:
        if v.name in seen:
            raise IRError(f"duplicate value name {v.name}")
        seen[v.name] = v
    for ins in prog.instrs:
        for a in ins.args:
            if seen.get(a.name) is None:
                raise IRError(f"{ins}: operand {a.name} is not defined")
            if seen[a.name].width != a.width:
                raise IRError(f"{ins}: operand {a.name} width {a.width} != {seen[a.name].width}")
        _check_shape(ins)
        if ins.result is not None:
            if ins.result.name in seen:
                raise IRError(f"{ins}: {ins.result.name} assigned twice")
            seen[ins.result.name] = ins.result


def _check_shape(ins: Instr) -> None:
    op, args, r = ins.op, ins.args, ins.result
    def need(n):
        if len(args) != n:
            raise IRError(f"{ins}: {op} takes {n} operand(s)")
    if op == "const":
        need(0)
        if ins.value is None or r is None:
            raise IRError(f"{ins}: const needs a value")
        if not r.lo <= ins.value <= r.hi:
            raise IRError(f"{ins}: {ins.value} outside {r}")
    elif op in BINARY:
        need(2)
        if args[0].width != args[1].width or r.width != args[0].width:
            raise IRError(f"{ins}: {op} needs equal widths")
        if op in ("add", "sub", "mul") and args[0].signed != args[1].signed:
            raise IRError(f"{ins}: {op} operands differ in signedness; bridge first (L10)")
    elif op in UNARY:
        need(1)
        if r.width != args[0].width:
            raise IRError(f"{ins}: {op} preserves width")
    elif op in SHIFTS:
        need(1)
        if ins.k is None or not 0 <= ins.k < args[0].width:
            raise IRError(f"{ins}: shift amount must be a constant in [0, {args[0].width})")
        if r.width != args[0].width:
            raise IRError(f"{ins}: {op} preserves width")
        if op == "ashr" and not args[0].signed:
            raise IRError(f"{ins}: ashr reads its operand as signed")
        if op == "lshr" and args[0].signed:
            raise IRError(f"{ins}: lshr reads its operand as unsigned")
    elif op in CASTS:
        need(1)
        if r.width <= args[0].width:
            raise IRError(f"{ins}: {op} must widen")
        if op == "sext" and not (args[0].signed and r.signed):
            raise IRError(f"{ins}: sext is signed -> signed")
        if op == "zext" and (args[0].signed or r.signed):
            raise IRError(f"{ins}: zext is unsigned -> unsigned")
    elif op == "extract":
        need(1)
        if ins.hi is None or ins.lo is None or not 0 <= ins.lo <= ins.hi < args[0].width:
            raise IRError(f"{ins}: bad extract range")
        if r.width != ins.hi - ins.lo + 1:
            raise IRError(f"{ins}: extract width mismatch")
    elif op == "cmp":
        need(2)
        if ins.pred not in CMP_PREDS:
            raise IRError(f"{ins}: unknown predicate {ins.pred}")
        if args[0].width != args[1].width:
            raise IRError(f"{ins}: cmp needs equal widths")
        if r.width != 1 or r.signed:
            raise IRError(f"{ins}: cmp produces an unsigned 1-bit value")
    elif op == "ite":
        need(3)
        if args[0].width != 1:
            raise IRError(f"{ins}: ite condition must be 1-bit")
        if args[1].width != args[2].width or r.width != args[1].width:
            raise IRError(f"{ins}: ite arms must match the result width")
        if args[1].signed != args[2].signed or r.signed != args[1].signed:
            raise IRError(f"{ins}: ite arms must agree in signedness")
    elif op == "marker":
        need(0)
        if r is not None or ins.tag is None:
            raise IRError(f"{ins}: marker has a tag and no result")
    else:
        raise IRError(f"unknown op {op}")


class Builder:
    """Convenience builder; names temporaries t0, t1, … (M7)."""

    def __init__(self, prefix: str = "t"):
        self.prog = Program()
        self.prefix = prefix
        self._n = 0

    def _fresh(self, width: int, signed: bool, kind: str = "temp") -> Value:
        v = Value(f"{self.prefix}{self._n}", width, signed, kind)
        self._n += 1
        return v

    def input(self, name: str, width: int, signed: bool) -> Value:
        v = Value(name, width, signed, "input")
        self.prog.inputs.append(v)
        return v

    def _emit(self, ins: Instr) -> Value | None:
        _check_shape(ins)
        self.prog.instrs.append(ins)
        return ins.result

    def const(self, value: int, width: int, signed: bool) -> Value:
        return self._emit(Instr("const", self._fresh(width, signed, "const"), value=value))

    def binop(self, op: str, a: Value, b: Value) -> Value:
        return self._emit(Instr(op, self._fresh(a.width, a.signed), (a, b)))

    def add(self, a, b): return self.binop("add", a, b)
    def sub(self, a, b): return self.binop("sub", a, b)
    def mul(self, a, b): return self.binop("mul", a, b)
    def and_(self, a, b): return self.binop("and", a, b)
    def or_(self, a, b): return self.binop("or", a, b)
    def xor(self, a, b): return self.binop("xor", a, b)

    def neg(self, a): return self._emit(Instr("neg", self._fresh(a.width, a.signed), (a,)))
    def not_(self, a): return self._emit(Instr("not", self._fresh(a.width, a.signed), (a,)))

    def shl(self, a, k): return self._emit(Instr("shl", self._fresh(a.width, a.signed), (a,), k=k))
    def ashr(self, a, k): return self._emit(Instr("ashr", self._fresh(a.width, True), (a,), k=k))
    def lshr(self, a, k): return self._emit(Instr("lshr", self._fresh(a.width, False), (a,), k=k))

    def sext(self, a, width): return self._emit(Instr("sext", self._fresh(width, True), (a,), k=width))
    def zext(self, a, width): return self._emit(Instr("zext", self._fresh(width, False), (a,), k=width))

    def extract(self, a, hi, lo, signed=None):
        w = hi - lo + 1
        s = a.signed if signed is None else signed
        return self._emit(Instr("extract", self._fresh(w, s), (a,), hi=hi, lo=lo))

    def cmp(self, pred, a, b):
        return self._emit(Instr("cmp", self._fresh(1, False), (a, b), pred=pred))

    def ite(self, c, a, b):
        return self._emit(Instr("ite", self._fresh(a.width, a.signed), (c, a, b)))

    def marker(self, tag: str):
        return self._emit(Instr("marker", None, tag=tag))

    def build(self) -> Program:
        check(self.prog)
        return self.prog
