"""Specification self-checks S1–S5 (spec §4.4).

S1 every reference resolves at the time point it names
S2 an eqmod has at most two moduli (extend_z3 only compiles eqmodP1/eqmodP2, §1.3)
S3 an NTT schedule is consistent (checked where the schedule is built, lib/ntt.py)
S4 a ghost is bound exactly once and only mentions entry values
S5 the specification holds on concrete runs — that is gate G4, not a static check
"""
from __future__ import annotations

from dataclasses import dataclass

from ..ir.trace import ENTRY, Trace
from . import dsl


@dataclass
class Failure:
    check: str
    message: str

    def __str__(self) -> str:
        return f"{self.check}: {self.message}"


def check_spec(target: dsl.Target, trace: Trace | None = None) -> list[Failure]:
    """S1, S2 and S4. S1 needs the trace; without one it is skipped."""
    out: list[Failure] = []
    out += _s1(target, trace) if trace is not None else []
    out += _s2(target)
    out += _s4(target)
    return out


def _assertions(target: dsl.Target):
    """(point, assertion) for everything the target states."""
    for point in target.points():
        ranges, algs = target.assertions_at(point)
        for a in list(ranges) + list(algs):
            yield point, a


def _exprs(assertion):
    if isinstance(assertion, dsl.RangeAssert):
        return [assertion.expr, assertion.lo, assertion.hi]
    return [assertion.lhs, assertion.rhs] + list(assertion.mods)


def _s1(target: dsl.Target, trace: Trace) -> list[Failure]:
    out = []
    points = {s.point for s in trace.snapshots}
    for point, a in _assertions(target):
        for e in _exprs(a):
            for r in e.refs():
                if r.time is None:
                    out.append(Failure("S1", f"{r.obj}[{r.idx}] in `{a}` has no time point"))
                elif r.time not in points:
                    out.append(Failure("S1", f"`{a}` refers to {r.time}, which the trace "
                                             f"does not contain"))
                elif r.obj not in trace.objects:
                    out.append(Failure("S1", f"{r.obj} is not a registered object"))
                elif (r.obj, r.idx) not in trace.at(r.time).values:
                    out.append(Failure("S1", f"{r.obj}[{r.idx}] is not live at {r.time}"))
    for name, e in target.ghosts.items():
        for r in e.refs():
            if r.time is not None and r.time in points and r.obj in trace.objects \
                    and (r.obj, r.idx) not in trace.at(r.time).values:
                out.append(Failure("S1", f"ghost {name} reads {r.obj}[{r.idx}] at {r.time}, "
                                         "which is not live there"))
    return _dedup(out)


def _s2(target: dsl.Target) -> list[Failure]:
    out = []
    for point, a in _assertions(target):
        if isinstance(a, dsl.AlgAssert) and len(a.mods) > 2:
            out.append(Failure("S2", f"{len(a.mods)} moduli at {point}: extend_z3 only has "
                                     f"eqmodP1 and eqmodP2 (§1.3); `{a}`"))
    return out


def _s4(target: dsl.Target) -> list[Failure]:
    out = []
    used = set()
    for _, a in _assertions(target):
        for e in _exprs(a):
            used |= {g.name for g in e.ghosts()}
    for name, e in target.ghosts.items():
        for r in e.refs():
            if r.time is None:
                out.append(Failure("S4", f"ghost {name} has an un-timed reference to "
                                         f"{r.obj}[{r.idx}]"))
            elif r.time.kind != ENTRY:
                out.append(Failure("S4", f"ghost {name} reads {r.obj}[{r.idx}] at {r.time}; "
                                         "a ghost may only read entry values"))
        for g in e.ghosts():
            out.append(Failure("S4", f"ghost {name} is defined in terms of ghost {g.name}"))
    for name in used - set(target.ghosts):
        out.append(Failure("S4", f"ghost {name} is used but never bound"))
    return _dedup(out)


def _dedup(items: list[Failure]) -> list[Failure]:
    seen, out = set(), []
    for f in items:
        if str(f) not in seen:
            seen.add(str(f))
            out.append(f)
    return out
