"""Idioms the lowering recognises (spec §6.3).

A rule looks at one instruction; an idiom is a shape spread over several. The one that
matters here is the branch-free conditional move, `(m & a) | (~m & b)`, which §6.3 lists
as the second form of L12. Without it the `or` and the two `and`s are algebraically free
(L13) and the algebraic model says nothing at all about the result — which is exactly
what fiat-crypto's `cmovznz` is made of.
"""
from __future__ import annotations

from ..ir.ops import Instr, Program, Value


def defs(prog: Program) -> dict:
    """value name -> the instruction that defines it."""
    return {i.result.name: i for i in prog.instrs if i.result is not None}


def mask_select(ins: Instr, definitions: dict,
                masks: set | None = None) -> tuple[Value, Value, Value] | None:
    """`r = (m & a) | (~m & b)` -> (m, a, b), in whichever order it was written.

    The result is the value selected by the mask: `a` when m is all ones, `b` when m is
    zero — which is only true if m really is all ones or all zero. The shape alone does
    not say so, and asserting the equation anyway would put a false statement in the
    algebraic model, so the interval analysis has to have established it (§6.3's H2).
    The range VC still gets the obligation, the same bargain as an EXACT decision."""
    if ins.op != "or":
        return None
    left, right = (definitions.get(a.name) for a in ins.args)
    if left is None or right is None or left.op != "and" or right.op != "and":
        return None
    for x, y in ((left, right), (right, left)):
        for mi in (0, 1):
            m, a = x.args[mi], x.args[1 - mi]
            for ni in (0, 1):
                negated, b = y.args[ni], y.args[1 - ni]
                d = definitions.get(negated.name)
                if d is not None and d.op == "not" and d.args[0].name == m.name \
                        and (masks is None or m.name in masks):
                    return m, a, b
    return None
