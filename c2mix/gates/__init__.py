"""Verification gates (spec §8.1). G1 is `c2mix lint`, G2 arrives with the C frontend,
G10 is a grep over the core; the rest live here."""
from __future__ import annotations

import random

from ..ir import interp
from ..ir.trace import ENTRY_POINT, Trace
from ..spec import dsl
from ..spec.evalspec import Run, holds
from ..vc.assemble import entry_intervals


def sample_inputs(trace: Trace, target: dsl.Target, rng: random.Random,
                  tries: int = 200) -> dict[str, int] | None:
    """Random inputs that satisfy the precondition (rejection sampling, guided by the
    per-value intervals the precondition implies)."""
    bounds = entry_intervals(target, trace, ENTRY_POINT)
    for _ in range(tries):
        values = {}
        for v in trace.prog.inputs:
            span = bounds.get(v.name)
            values[v.name] = rng.randint(span.lo, span.hi) if span else rng.randint(v.lo, v.hi)
        patterns = interp.run(trace.prog, values)
        run = Run(trace, patterns)
        if all(holds(a, run, target.ghosts) for a in target.pre_ranges + target.pre_algs):
            return values
    return None


def runs(trace: Trace, target: dsl.Target, n: int, seed: int = 0):
    """n concrete executions whose inputs satisfy the precondition."""
    rng = random.Random(seed)
    out = []
    for _ in range(n):
        values = sample_inputs(trace, target, rng)
        if values is None:
            raise RuntimeError("could not find inputs satisfying the precondition")
        out.append((values, interp.run(trace.prog, values)))
    return out
