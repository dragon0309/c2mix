"""Evaluate a specification on one concrete run (spec §8.1, gates G3 and G4).

Expressions evaluate to univariate integer polynomials: a plain integer is a constant
polynomial, an indeterminate is x. Congruences follow §8.1:

  * integer moduli — divisibility;
  * (prime q, monic m(x)) — reduce modulo m(x) over ℤ, then check q divides every
    coefficient;
  * a modulus that is a program variable evaluates to an integer, so it is the first case.

Anything else is reported as `unsupported-eval` rather than silently passed.
"""
from __future__ import annotations

from dataclasses import dataclass

from ..ir.interp import interpret
from ..ir.trace import Point, Trace
from . import dsl


class UnsupportedEval(Exception):
    pass


@dataclass(frozen=True)
class Poly:
    """Univariate polynomial with integer coefficients; coeffs[i] is the xⁱ term."""
    coeffs: tuple
    var: str | None = None

    @staticmethod
    def const(n: int) -> "Poly":
        return Poly((n,) if n else ())

    @staticmethod
    def x(name: str) -> "Poly":
        return Poly((0, 1), name)

    def _var_with(self, o: "Poly") -> str | None:
        if self.var and o.var and self.var != o.var:
            raise UnsupportedEval(f"two indeterminates in one expression: {self.var}, {o.var}")
        return self.var or o.var

    def is_const(self) -> bool:
        return len(self.coeffs) <= 1

    def value(self) -> int:
        if not self.is_const():
            raise UnsupportedEval("expected an integer, got a polynomial")
        return self.coeffs[0] if self.coeffs else 0

    def __add__(self, o: "Poly") -> "Poly":
        n = max(len(self.coeffs), len(o.coeffs))
        out = [self._get(i) + o._get(i) for i in range(n)]
        return Poly(_trim(out), self._var_with(o))

    def __sub__(self, o: "Poly") -> "Poly":
        n = max(len(self.coeffs), len(o.coeffs))
        out = [self._get(i) - o._get(i) for i in range(n)]
        return Poly(_trim(out), self._var_with(o))

    def __mul__(self, o: "Poly") -> "Poly":
        if not self.coeffs or not o.coeffs:
            return Poly((), self._var_with(o))
        out = [0] * (len(self.coeffs) + len(o.coeffs) - 1)
        for i, a in enumerate(self.coeffs):
            if a:
                for j, b in enumerate(o.coeffs):
                    out[i + j] += a * b
        return Poly(_trim(out), self._var_with(o))

    def __pow__(self, k: int) -> "Poly":
        out = Poly.const(1)
        for _ in range(k):
            out = out * self
        return out

    def _get(self, i: int) -> int:
        return self.coeffs[i] if i < len(self.coeffs) else 0

    @property
    def degree(self) -> int:
        return len(self.coeffs) - 1

    def __str__(self) -> str:
        if not self.coeffs:
            return "0"
        return " + ".join(f"{c}·{self.var or 'x'}^{i}" if i else str(c)
                          for i, c in enumerate(self.coeffs) if c)


def _trim(coeffs) -> tuple:
    out = list(coeffs)
    while out and out[-1] == 0:
        out.pop()
    return tuple(out)


def rem_monic(a: Poly, m: Poly) -> Poly:
    """a mod m for monic m; exact over ℤ."""
    if not m.coeffs or m.coeffs[-1] != 1:
        raise UnsupportedEval(f"modulus polynomial is not monic: {m}")
    out = list(a.coeffs)
    d = m.degree
    for i in range(len(out) - 1, d - 1, -1):
        c = out[i]
        if c:
            out[i] = 0
            for j in range(d):
                out[i - d + j] -= c * m.coeffs[j]
    return Poly(_trim(out), a.var or m.var)


# ---------------------------------------------------------------- evaluation
class Run:
    """One concrete execution: the trace plus the bit patterns of every value."""

    def __init__(self, trace: Trace, patterns: dict[str, int]):
        self.trace = trace
        self.patterns = patterns

    def ref(self, r: dsl.Ref) -> int:
        if r.time is None:
            raise UnsupportedEval(f"{r} has no time point (S1)")
        v = self.trace.value(r.time, r.obj, r.idx)
        return interpret(self.patterns[v.name], v.width, v.signed)


def evaluate(e: dsl.Expr, run: Run, ghosts: dict[str, dsl.Expr] | None = None) -> Poly:
    ghosts = ghosts or {}
    if isinstance(e, dsl.Const):
        return Poly.const(e.value)
    if isinstance(e, dsl.Ref):
        return Poly.const(run.ref(e))
    if isinstance(e, dsl.Indet):
        return Poly.x(e.name)
    if isinstance(e, dsl.Ghost):
        if e.name not in ghosts:
            raise UnsupportedEval(f"ghost {e.name} is not bound (S4)")
        return evaluate(ghosts[e.name], run, ghosts)
    if isinstance(e, dsl.Bin):
        a, b = evaluate(e.a, run, ghosts), evaluate(e.b, run, ghosts)
        return {"+": a.__add__, "-": a.__sub__, "*": a.__mul__}[e.op](b)
    if isinstance(e, dsl.Pow):
        return evaluate(e.base, run, ghosts) ** e.k
    raise UnsupportedEval(f"cannot evaluate {e!r}")


def holds(assertion, run: Run, ghosts=None) -> bool:
    """True when the assertion holds on this run. Raises UnsupportedEval if §8.1 has
    no decision procedure for it."""
    if isinstance(assertion, dsl.RangeAssert):
        e = evaluate(assertion.expr, run, ghosts).value()
        lo = evaluate(assertion.lo, run, ghosts).value()
        hi = evaluate(assertion.hi, run, ghosts).value()
        return lo <= e < hi
    a = evaluate(assertion.lhs, run, ghosts)
    b = evaluate(assertion.rhs, run, ghosts)
    diff = a - b
    if assertion.kind == "eq":
        return not diff.coeffs
    mods = [evaluate(m, run, ghosts) for m in assertion.mods]
    if len(mods) > 2:
        raise UnsupportedEval("more than two moduli (S2)")
    ints = [m for m in mods if m.is_const()]
    polys = [m for m in mods if not m.is_const()]
    for m in polys:
        diff = rem_monic(diff, m)
    if not ints:
        return not diff.coeffs
    if len(ints) > 1:
        raise UnsupportedEval("more than one integer modulus")
    q = ints[0].value()
    if q == 0:
        raise UnsupportedEval("modulus 0")
    return all(c % q == 0 for c in diff.coeffs)
