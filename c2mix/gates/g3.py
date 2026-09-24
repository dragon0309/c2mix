"""G3 — trace consistency: a real execution is a model of every VC's premises.

For each run that satisfies the precondition, give every symbol of a VC the value it
has in that run (program values from the interpreter, witnesses and aliases from their
defining statements, ghosts from their bound expressions) and evaluate every
non-goal statement. All of them must be true.

This is what catches vacuity: if a premise were contradictory the VC would be `unsat`
for the wrong reason, and no real run could satisfy it.
"""
from __future__ import annotations

from ..ir.trace import Trace
from ..lower import evaluate
from ..spec import dsl
from ..spec.evalspec import Poly, Run, evaluate as eval_spec
from ..vc.assemble import VC


def env_for(vc: VC, trace: Trace, target: dsl.Target, patterns: dict[str, int]) -> evaluate.Env:
    widths = evaluate.widths_of(vc.seg)
    env = evaluate.Env({k: v for k, v in patterns.items() if k in widths}, widths)
    run = Run(trace, patterns)
    for name in target.ghosts:
        env.polys[name] = eval_spec(target.ghosts[name], run, target.ghosts)
    evaluate.solve_definitions(vc.seg, env)
    return env


def check(vcs: list[VC], trace: Trace, target: dsl.Target, patterns: dict[str, int]) -> list[str]:
    """Failures for one run; empty means this run is a model of every VC's premises."""
    from ..mixfmt.writer import to_str
    bad: list[str] = []
    for vc in vcs:
        env = env_for(vc, trace, target, patterns)
        for kind, statements in (("range statement", vc.seg.bv),
                                 ("algebraic statement", vc.seg.alg),
                                 ("safety obligation", vc.seg.safety),
                                 ("range premise", vc.premise_range),
                                 ("algebraic premise", vc.premise_alg),
                                 ("ghost binding", vc.ghost_bindings),
                                 ("hint", [h.bv_term() for h in vc.hints]),
                                 ("goal", vc.goal_alg + vc.goal_range)):
            for st in statements:
                got = evaluate.eval_term(st, env)
                if got[0] != "bool":
                    bad.append(f"cut{vc.index} {kind}: not a formula: {to_str(st)[:100]}")
                elif not got[1]:
                    bad.append(f"cut{vc.index} {kind} false on this run: {to_str(st)[:160]}")
    return bad


def check_runs(vcs: list[VC], trace: Trace, target: dsl.Target, executions) -> list[str]:
    out = []
    for values, patterns in executions:
        bad = check(vcs, trace, target, patterns)
        if bad:
            return bad + [f"inputs: {values}"]
    return out
