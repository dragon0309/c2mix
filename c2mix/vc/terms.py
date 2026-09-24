"""Compile specification expressions into the two models (spec §6.1, §7.3).

A specification talks about integers; a VC has to state the same thing twice:

  * in the range model, as bit-vector arithmetic at a width wide enough that nothing
    wraps (the golden files do the same: a 4-limb bound is stated at 256 bits);
  * in the algebraic model, as Poly terms, with indeterminates as (PVar "…") (D5).

The width comes from interval analysis of the expression, so the bound is exact
rather than guessed.
"""
from __future__ import annotations

from ..ir import intervals as iv
from ..ir.trace import Trace
from ..lower import encode as E
from ..lower.encode import Encoder
from ..spec import dsl


class TermError(Exception):
    pass


def _resolve(ref: dsl.Ref, trace: Trace):
    if ref.time is None:
        raise TermError(f"{ref} has no time point (S1)")
    return trace.value(ref.time, ref.obj, ref.idx)


# ---------------------------------------------------------------- intervals
def interval_of(e: dsl.Expr, trace: Trace, analysis: iv.Analysis) -> iv.Interval:
    """Interval of a specification expression, from the intervals of the values it
    reads. Indeterminates have no interval, so expressions containing them are
    algebraic-only."""
    if isinstance(e, dsl.Const):
        return iv.Interval(e.value, e.value)
    if isinstance(e, dsl.Ref):
        v = _resolve(e, trace)
        return analysis.intervals.get(v.name, iv.full(v))
    if isinstance(e, dsl.Bin):
        a, b = interval_of(e.a, trace, analysis), interval_of(e.b, trace, analysis)
        return {"+": a.__add__, "-": a.__sub__, "*": a.__mul__}[e.op](b)
    if isinstance(e, dsl.Pow):
        base = interval_of(e.base, trace, analysis)
        out = iv.Interval(1, 1)
        for _ in range(e.k):
            out = out * base
        return out
    raise TermError(f"{e} has no interval (indeterminate or ghost)")


def width_for(*intervals: iv.Interval) -> int:
    """Smallest width whose signed range holds all of them, rounded up to a multiple
    of 8 so the constants stay readable."""
    need = 1
    for i in intervals:
        for x in (i.lo, i.hi):
            need = max(need, x.bit_length() + 1 if x >= 0 else (-x - 1).bit_length() + 1)
    return max(8, (need + 7) // 8 * 8)


# ---------------------------------------------------------------- range model
def const_value(e: dsl.Expr) -> int | None:
    """The value of an expression that mentions no program value, else None."""
    if isinstance(e, dsl.Const):
        return e.value
    if isinstance(e, dsl.Bin):
        a, b = const_value(e.a), const_value(e.b)
        return None if a is None or b is None else {"+": a + b, "-": a - b, "*": a * b}[e.op]
    if isinstance(e, dsl.Pow):
        base = const_value(e.base)
        return None if base is None else base ** e.k
    return None


def to_bv(e: dsl.Expr, trace: Trace, enc: Encoder, width: int):
    """Bit-vector term for a specification expression, at `width` bits (signed)."""
    folded = const_value(e)
    if folded is not None:
        return E.bv_const(folded, width)
    if isinstance(e, dsl.Ref):
        v = _resolve(e, trace)
        kind = "sign_extend" if v.signed else "zero_extend"
        if v.width > width:
            raise TermError(f"{v} is wider than the {width}-bit range term")
        return E.extend(kind, width - v.width, enc.bv(v)) if v.width < width else enc.bv(v)
    if isinstance(e, dsl.Bin):
        op = {"+": "bvadd", "-": "bvsub", "*": "bvmul"}[e.op]
        return [op, to_bv(e.a, trace, enc, width), to_bv(e.b, trace, enc, width)]
    if isinstance(e, dsl.Pow):
        out = to_bv(e.base, trace, enc, width)
        for _ in range(e.k - 1):
            out = ["bvmul", out, to_bv(e.base, trace, enc, width)]
        return out
    raise TermError(f"cannot state {e} in the range model")


def value_width(e: dsl.Expr, trace: Trace) -> int:
    """The widest program value the expression reads (the term cannot be narrower)."""
    return max((_resolve(r, trace).width for r in e.refs()), default=1)


def range_assert_bv(a: dsl.RangeAssert, trace: Trace, enc: Encoder,
                    analysis: iv.Analysis):
    """lo ≤ e < hi as one bit-vector formula, wide enough not to wrap."""
    spans = [interval_of(x, trace, analysis) for x in (a.expr, a.lo, a.hi)]
    width = max(width_for(*spans),
                *(value_width(x, trace) for x in (a.expr, a.lo, a.hi)))
    e, lo, hi = (to_bv(x, trace, enc, width) for x in (a.expr, a.lo, a.hi))
    return ["and", ["bvsle", lo, e], ["bvslt", e, hi]]


# ---------------------------------------------------------------- algebraic model
def to_poly(e: dsl.Expr, trace: Trace, enc: Encoder, ghosts: dict | None = None,
            inline_ghosts: bool = False):
    ghosts = ghosts or {}
    folded = const_value(e)
    if folded is not None:
        return E.PInt(folded)
    if isinstance(e, dsl.Ref):
        return E.PConst(enc.atom(_resolve(e, trace)))
    if isinstance(e, dsl.Indet):
        return ["PVar", f'"{e.name}"']
    if isinstance(e, dsl.Ghost):
        if inline_ghosts:
            if e.name not in ghosts:
                raise TermError(f"ghost {e.name} is not bound (S4)")
            return to_poly(ghosts[e.name], trace, enc, ghosts, inline_ghosts)
        return e.name
    if isinstance(e, dsl.Bin):
        op = {"+": E.PAdd, "-": E.PSub, "*": E.PMul}[e.op]
        return op(to_poly(e.a, trace, enc, ghosts, inline_ghosts),
                  to_poly(e.b, trace, enc, ghosts, inline_ghosts))
    if isinstance(e, dsl.Pow):
        return E.PPow(to_poly(e.base, trace, enc, ghosts, inline_ghosts), e.k)
    raise TermError(f"cannot state {e} in the algebraic model")


def alg_assert_poly(a: dsl.AlgAssert, trace: Trace, enc: Encoder, ghosts=None,
                    inline_ghosts=False):
    """eq → eqP, eqmod → eqmodP1/eqmodP2 (M3: at most two moduli, S2 checks that)."""
    lhs = to_poly(a.lhs, trace, enc, ghosts, inline_ghosts)
    rhs = to_poly(a.rhs, trace, enc, ghosts, inline_ghosts)
    if a.kind == "eq":
        return E.eqP(lhs, rhs)
    mods = [to_poly(m, trace, enc, ghosts, inline_ghosts) for m in a.mods]
    if not 1 <= len(mods) <= 2:
        raise TermError(f"eqmod needs one or two moduli, got {len(mods)} (S2)")
    return [f"eqmodP{len(mods)}", lhs, rhs] + mods


def values_of(a, trace: Trace) -> set:
    """The SSA values an assertion mentions (used by fact carrying, §7.2)."""
    exprs = ([a.expr, a.lo, a.hi] if isinstance(a, dsl.RangeAssert)
             else [a.lhs, a.rhs] + list(a.mods))
    out = set()
    for e in exprs:
        for r in e.refs():
            try:
                out.add(_resolve(r, trace).name)
            except (KeyError, TermError):
                pass
    return out
