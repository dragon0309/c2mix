"""Concrete interpreter for the c2mix IR.

Values are kept as bit patterns (unsigned int < 2^w); `interpret` reads a pattern
as the integer its signedness says. This is the reference semantics that G3 and the
phase-1 fuzzing check the lowering against.
"""
from __future__ import annotations

from .ops import Instr, Program, Value


class TrapError(Exception):
    """The program did something the model does not define (never happens for
    well-formed IR; kept so the interpreter fails loudly instead of silently)."""


def mask(w: int) -> int:
    return (1 << w) - 1


def interpret(pattern: int, width: int, signed: bool) -> int:
    if signed and pattern >> (width - 1):
        return pattern - (1 << width)
    return pattern


def encode(value: int, width: int) -> int:
    return value & mask(width)


def fits(value: int, width: int, signed: bool) -> bool:
    lo = -(1 << (width - 1)) if signed else 0
    hi = (1 << (width - 1)) - 1 if signed else (1 << width) - 1
    return lo <= value <= hi


def eval_instr(ins: Instr, env: dict[str, int]) -> int | None:
    """Bit pattern of the result, or None for marker."""
    a = [env[v.name] for v in ins.args]
    op, r = ins.op, ins.result
    w = r.width if r is not None else 0
    if op == "const":
        return encode(ins.value, w)
    if op == "add":
        return (a[0] + a[1]) & mask(w)
    if op == "sub":
        return (a[0] - a[1]) & mask(w)
    if op == "mul":
        return (a[0] * a[1]) & mask(w)
    if op == "and":
        return a[0] & a[1]
    if op == "or":
        return a[0] | a[1]
    if op == "xor":
        return a[0] ^ a[1]
    if op == "neg":
        return (-a[0]) & mask(w)
    if op == "not":
        return (~a[0]) & mask(w)
    if op == "shl":
        return (a[0] << ins.k) & mask(w)
    if op == "lshr":
        return a[0] >> ins.k
    if op == "ashr":
        src = ins.args[0]
        return encode(interpret(a[0], src.width, True) >> ins.k, w)
    if op == "sext":
        return encode(interpret(a[0], ins.args[0].width, True), w)
    if op == "zext":
        return a[0]
    if op == "extract":
        return (a[0] >> ins.lo) & mask(w)
    if op == "cmp":
        s = ins.pred in ("slt", "sle", "sgt", "sge")
        x = interpret(a[0], ins.args[0].width, s)
        y = interpret(a[1], ins.args[1].width, s)
        if ins.pred in ("ult", "slt"):
            return int(x < y)
        if ins.pred in ("ule", "sle"):
            return int(x <= y)
        if ins.pred in ("ugt", "sgt"):
            return int(x > y)
        if ins.pred in ("uge", "sge"):
            return int(x >= y)
        return int(x == y) if ins.pred == "eq" else int(x != y)
    if op == "ite":
        return a[1] if a[0] else a[2]
    if op == "marker":
        return None
    raise TrapError(f"unknown op {op}")


def run(prog: Program, inputs: dict[str, int]) -> dict[str, int]:
    """Run with `inputs` given as interpreted integers, keyed by input name.
    Returns bit patterns for every value."""
    env: dict[str, int] = {}
    for v in prog.inputs:
        if v.name not in inputs:
            raise TrapError(f"missing input {v.name}")
        if not fits(inputs[v.name], v.width, v.signed):
            raise TrapError(f"input {v.name}={inputs[v.name]} outside {v}")
        env[v.name] = encode(inputs[v.name], v.width)
    for ins in prog.instrs:
        out = eval_instr(ins, env)
        if ins.result is not None:
            env[ins.result.name] = out
    return env


def values_of(prog: Program, env: dict[str, int]) -> dict[str, int]:
    """Interpreted integers (signed where the value says so)."""
    return {v.name: interpret(env[v.name], v.width, v.signed) for v in prog.values()
            if v.name in env}


def read(env: dict[str, int], v: Value, signed: bool | None = None) -> int:
    return interpret(env[v.name], v.width, v.signed if signed is None else signed)
