"""Fact carrying (spec §7.2).

SSA values are never overwritten, so an assertion proved at an earlier cut still holds
later. VCᵢ may therefore assume, besides Cᵢ, any earlier conclusion that is *relevant*:
one that mentions an SSA value the segment reads or that the next assertion set
mentions. Ghost references do not count as relevance.

Soundness needs only one thing, which G9 checks: every carried fact is the conclusion
of some earlier VC (or part of the precondition).
"""
from __future__ import annotations

from ..ir.trace import Trace
from ..spec import dsl
from . import terms

MODES = ("relevant", "previous", "all")


def segment_values(trace: Trace, span: tuple[int, int]) -> set[str]:
    """Names of the SSA values the segment reads or defines."""
    lo, hi = span
    out: set[str] = set()
    for ins in trace.prog.instrs[lo:hi]:
        out |= {a.name for a in ins.args}
        if ins.result is not None:
            out.add(ins.result.name)
    return out


def carried_facts(trace: Trace, target: dsl.Target, i: int, spans, mode: str = "relevant"):
    """(range asserts, algebraic asserts, provenance) to add to VCᵢ's premises."""
    if mode not in MODES:
        raise ValueError(f"unknown carry mode {mode}")
    p_from, p_to, span = spans[i]
    earlier = [p for p, _, _ in spans[:i]]
    if not earlier:
        return [], [], []
    if mode == "previous":
        earlier = earlier[-1:]

    relevant_values = segment_values(trace, span)
    next_ranges, next_algs = target.assertions_at(p_to)
    for a in list(next_ranges) + list(next_algs):
        relevant_values |= terms.values_of(a, trace)

    out_r, out_a, provenance = [], [], []
    for point in earlier:
        ranges, algs = target.assertions_at(point)
        for a in ranges:
            if _keep(a, trace, relevant_values, mode):
                out_r.append(a)
                provenance.append((str(point), str(a)))
        for a in algs:
            if _keep(a, trace, relevant_values, mode):
                out_a.append(a)
                provenance.append((str(point), str(a)))
    return out_r, out_a, provenance


def _keep(a, trace: Trace, relevant: set[str], mode: str) -> bool:
    if mode == "all" or mode == "previous":
        return True
    return bool(terms.values_of(a, trace) & relevant)
