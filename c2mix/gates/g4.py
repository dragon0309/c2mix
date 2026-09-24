"""G4 — the specification itself holds on real executions (spec §8.1, S5)."""
from __future__ import annotations

from ..ir.trace import Trace
from ..spec import dsl
from ..spec.evalspec import Run, UnsupportedEval, holds


def check(trace: Trace, target: dsl.Target, patterns: dict[str, int]) -> tuple[list[str], list[str]]:
    """(failures, assertions with no decision procedure). The precondition is assumed:
    callers pass runs that satisfy it."""
    run = Run(trace, patterns)
    bad, unsupported = [], []
    for point in target.points():
        ranges, algs = target.assertions_at(point)
        for a in list(ranges) + list(algs):
            try:
                if not holds(a, run, target.ghosts):
                    bad.append(f"{point}: {a}")
            except UnsupportedEval as e:
                unsupported.append(f"{point}: {a} ({e})")
    return bad, unsupported


def check_runs(trace: Trace, target: dsl.Target, executions):
    unsupported: list[str] = []
    for values, patterns in executions:
        bad, un = check(trace, target, patterns)
        unsupported = un
        if bad:
            return bad + [f"inputs: {values}"], unsupported
    return [], unsupported
