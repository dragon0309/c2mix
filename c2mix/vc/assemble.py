"""Assemble verification conditions from a trace and a specification (spec §7.1).

The trace is cut at the markers into segments S₀…S_K. For each segment the VC says:
assuming the assertions that hold at its start (plus facts carried from earlier, §7.2),
and assuming the segment's own statements, the assertions at its end follow.

    cut{i}.smt2        Rᵢ, Aᵢ, carried | BV(Sᵢ), ALG(Sᵢ) | ¬Aᵢ₊₁
    cut{i}.range.smt2  Rᵢ, carried     | BV(Sᵢ)          | ¬(Rᵢ₊₁ ∧ safety ∧ hints)
"""
from __future__ import annotations

from dataclasses import dataclass, field

from ..ir import intervals as iv
from ..ir.trace import ENTRY_POINT, Point, Trace
from ..lower import encode as E
from ..lower import rules
from ..lower.encode import Encoder, Segment
from ..spec import dsl
from . import carry as carry_mod
from . import terms


@dataclass
class Options:
    int_encoding: str = E.ALIAS          # alias | bv2int (D4)
    ghost: str = "bind"                  # bind | inline | legacy-pow2 (D8)
    exactness: str = "auto"              # auto | split (D6)
    hints: str = "omit"                  # omit | emit (§6.4)
    carry: str = "relevant"              # relevant | previous | all (§7.2)
    hint_timeout: float = 10.0
    hint_samples: int = 16               # runs that filter hint candidates (0: none)
    range_slices: bool = False           # choose a cone depth per range obligation (§7.4)
    copy_alias: bool = True              # copies reuse the atom they copy (§6.3)


@dataclass
class VC:
    index: int
    point_from: Point
    point_to: Point
    span: tuple[int, int]
    seg: Segment
    enc: Encoder
    premise_range: list = field(default_factory=list)
    premise_alg: list = field(default_factory=list)
    goal_alg: list = field(default_factory=list)
    goal_range: list = field(default_factory=list)
    ghost_bindings: list = field(default_factory=list)
    hints: list = field(default_factory=list)       # (symbol, value, poly term, bv term)
    depths: dict = field(default_factory=dict)      # range obligation -> cone depth (§7.4)
    carried: list = field(default_factory=list)     # (from point, assertion text)

    @property
    def trivial(self) -> bool:
        return not self.goal_alg


def segment_spans(trace: Trace) -> list[tuple[Point, Point, tuple[int, int]]]:
    """(start point, end point, instruction span) for S₀…S_K."""
    points = [s.point for s in trace.snapshots]
    idx = [s.instr_index for s in trace.snapshots]
    return [(points[i], points[i + 1], (idx[i], idx[i + 1])) for i in range(len(points) - 1)]


def entry_intervals(target: dsl.Target, trace: Trace, point: Point) -> dict[str, iv.Interval]:
    """Per-value intervals implied by the range assertions at `point`. Only assertions
    of the form lo ≤ single reference < hi give one; the rest still appear in the VC as
    premises, they just do not drive the EXACT/SPLIT decision (§6.2)."""
    out: dict[str, iv.Interval] = {}
    ranges, _ = target.assertions_at(point)
    for a in ranges:
        if not isinstance(a.expr, dsl.Ref):
            continue
        if not (isinstance(a.lo, dsl.Const) or _is_const_expr(a.lo)):
            continue
        if not (isinstance(a.hi, dsl.Const) or _is_const_expr(a.hi)):
            continue
        v = trace.value(a.expr.time, a.expr.obj, a.expr.idx)
        lo, hi = _const_value(a.lo), _const_value(a.hi) - 1
        got = iv.Interval(max(lo, v.lo), min(hi, v.hi))
        out[v.name] = got if v.name not in out else iv.Interval(
            max(out[v.name].lo, got.lo), min(out[v.name].hi, got.hi))
    return out


def _is_const_expr(e: dsl.Expr) -> bool:
    return not e.refs() and not e.indets() and not e.ghosts()


def _const_value(e: dsl.Expr) -> int:
    if isinstance(e, dsl.Const):
        return e.value
    if isinstance(e, dsl.Bin):
        a, b = _const_value(e.a), _const_value(e.b)
        return {"+": a + b, "-": a - b, "*": a * b}[e.op]
    if isinstance(e, dsl.Pow):
        return _const_value(e.base) ** e.k
    raise ValueError(f"{e} is not constant")


def assemble(trace: Trace, target: dsl.Target, opts: Options | None = None,
             z3_bin: str | None = None) -> list[VC]:
    opts = opts or Options()
    out: list[VC] = []
    spans = segment_spans(trace)
    known: dict[str, iv.Interval] = {}
    for i, (p_from, p_to, span) in enumerate(spans):
        pre_iv = {**known, **entry_intervals(target, trace, p_from)}
        analysis = iv.analyze(trace.prog, pre_iv if p_from == ENTRY_POINT else None,
                              force_split=opts.exactness == "split", span=span,
                              known=pre_iv)
        enc = Encoder(Segment(), opts.int_encoding, copy_alias=opts.copy_alias)
        seg = rules.lower(trace.prog, analysis, span=span, enc=enc)
        vc = VC(i, p_from, p_to, span, seg, enc)

        ranges_from, algs_from = target.assertions_at(p_from)
        ranges_to, algs_to = target.assertions_at(p_to)
        vc.premise_range = [terms.range_assert_bv(a, trace, enc, analysis) for a in ranges_from]
        vc.premise_alg = [terms.alg_assert_poly(a, trace, enc, target.ghosts,
                                                opts.ghost == "inline") for a in algs_from]
        vc.goal_alg = [terms.alg_assert_poly(a, trace, enc, target.ghosts,
                                             opts.ghost == "inline") for a in algs_to]
        vc.goal_range = [terms.range_assert_bv(a, trace, enc, analysis) for a in ranges_to]

        carried_r, carried_a, provenance = carry_mod.carried_facts(
            trace, target, i, spans, opts.carry)
        vc.premise_range += [terms.range_assert_bv(a, trace, enc, analysis) for a in carried_r]
        vc.premise_alg += [terms.alg_assert_poly(a, trace, enc, target.ghosts,
                                                 opts.ghost == "inline") for a in carried_a]
        vc.carried = provenance

        if opts.ghost == "bind":
            used = _ghosts_used(list(ranges_from) + list(algs_from) + list(ranges_to)
                                + list(algs_to) + list(carried_r) + list(carried_a))
            if p_from == ENTRY_POINT:
                for name in target.ghost_order:
                    body = terms.to_poly(target.ghosts[name], trace, enc, target.ghosts)
                    enc.seg.declare(name, ["Poly", "Int"])
                    vc.ghost_bindings.append(E.eqP(name, body))
            for name in used:                     # ghosts only mentioned here
                enc.seg.declare(name, ["Poly", "Int"])

        known = dict(analysis.intervals)
        out.append(vc)

    if opts.hints != "off":
        from . import hints as hints_mod
        runs = hints_mod.sample_runs(trace, target, opts.hint_samples)
        for vc in out:
            vc.hints = hints_mod.discover(vc, z3_bin or "z3", opts.hint_timeout,
                                          samples=hints_mod.sample_envs(vc, runs))
    if opts.range_slices:
        for vc in out:
            vc.depths = obligation_depths(vc, z3_bin or "z3", opts.hint_timeout)
    return out


SMALL_CONE = 60     # statements; an obligation this local keeps its whole cone


def obligation_depths(vc: VC, z3_bin: str, timeout: float) -> dict:
    """For a split range VC: the shallowest cone on which z3 proves each obligation
    whose whole cone is large (vc/prover.py). A shallower slice is a subset of the
    model, so G5 proving the obligation there proves it; an obligation no slice
    proves keeps its full cone and G5 decides it as before. Hints bring their own."""
    from ..mixfmt.writer import to_str
    from . import prover
    model = prover.RangeModel(vc.seg, vc.premise_range)
    goals = [g for g in list(vc.goal_range) + list(vc.seg.safety)
             if len(model.cone(g)[1]) > SMALL_CONE]
    prover.prove_all(model, goals, z3_bin, timeout, depths=prover.DEPTHS[:-1])
    return {to_str(g): model.depth_of[to_str(g)] for g in goals
            if to_str(g) in model.depth_of}


def _ghosts_used(assertions) -> list[str]:
    names = set()
    for a in assertions:
        exprs = ([a.expr, a.lo, a.hi] if isinstance(a, dsl.RangeAssert)
                 else [a.lhs, a.rhs] + list(a.mods))
        for e in exprs:
            names |= {g.name for g in e.ghosts()}
    return sorted(names)
