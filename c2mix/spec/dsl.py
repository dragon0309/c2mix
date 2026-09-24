"""The specification DSL (spec §4.3), embedded in Python (D3).

A specification says what the program's values mean (single integer, multi-limb
integer, polynomial) and what must hold about them (ranges, equalities, congruences)
at the entry, at each cut and at the exit. It never mentions bit-vectors: those come
from the trace, and the lowering relates the two.

Expressions are a small AST so the same specification can be
  * evaluated on a concrete run (G4, and G3's view of the premises),
  * emitted as Poly terms for the algebraic section, and
  * emitted as bit-vector bounds for the range section.
"""
from __future__ import annotations

from dataclasses import dataclass, field, replace

from ..ir.trace import CUT, ENTRY_POINT, EXIT_POINT, Point

# ---------------------------------------------------------------- expressions


class Expr:
    """Base class; arithmetic builds the AST, the time properties fill in when."""

    def __add__(self, o): return Bin("+", self, _lift(o))
    def __radd__(self, o): return Bin("+", _lift(o), self)
    def __sub__(self, o): return Bin("-", self, _lift(o))
    def __rsub__(self, o): return Bin("-", _lift(o), self)
    def __mul__(self, o): return Bin("*", self, _lift(o))
    def __rmul__(self, o): return Bin("*", _lift(o), self)
    def __neg__(self): return Bin("-", Const(0), self)
    def __pow__(self, k: int): return Pow(self, int(k))

    # comparisons build range assertions; see rng()
    def __le__(self, o): return _cmp(self, "<=", _lift(o))
    def __lt__(self, o): return _cmp(self, "<", _lift(o))
    def __ge__(self, o): return _cmp(_lift(o), "<=", self)
    def __gt__(self, o): return _cmp(_lift(o), "<", self)

    def at(self, point) -> "Expr":
        """Fill in every un-timed reference with this time point."""
        p = point.point if isinstance(point, Cut) else point
        return _map(self, lambda n: replace(n, time=p) if isinstance(n, Ref) and n.time is None else None)

    @property
    def entry(self) -> "Expr":
        return self.at(ENTRY_POINT)

    @property
    def exit(self) -> "Expr":
        return self.at(EXIT_POINT)

    def refs(self):
        out = []
        _map(self, lambda n: out.append(n) if isinstance(n, Ref) else None)
        return out

    def ghosts(self):
        out = []
        _map(self, lambda n: out.append(n) if isinstance(n, Ghost) else None)
        return out

    def indets(self):
        out = []
        _map(self, lambda n: out.append(n) if isinstance(n, Indet) else None)
        return out


@dataclass(frozen=True)
class Const(Expr):
    value: int

    def __str__(self): return str(self.value)


@dataclass(frozen=True)
class Ref(Expr):
    """One element of a registered object, at a time point (None until applied)."""
    obj: str
    idx: int = 0
    time: Point | None = None

    def __str__(self): return f"{self.obj}[{self.idx}]@{self.time}"


@dataclass(frozen=True)
class Indet(Expr):
    """A polynomial indeterminate (D5: always emitted as (PVar "…"))."""
    name: str

    def __str__(self): return self.name


@dataclass(frozen=True)
class Ghost(Expr):
    name: str

    def __str__(self): return f"ghost:{self.name}"


@dataclass(frozen=True)
class Bin(Expr):
    op: str
    a: Expr
    b: Expr

    def __str__(self): return f"({self.a} {self.op} {self.b})"


@dataclass(frozen=True)
class Pow(Expr):
    base: Expr
    k: int

    def __str__(self): return f"{self.base}^{self.k}"


def _lift(o) -> Expr:
    if isinstance(o, Expr):
        return o
    if isinstance(o, int):
        return Const(o)
    raise TypeError(f"cannot use {o!r} in a specification expression")


def _map(e: Expr, fn):
    """Rewrite bottom-up; fn returns a replacement or None. Also used to collect."""
    if isinstance(e, (Const, Ref, Indet, Ghost)):
        return fn(e) or e
    if isinstance(e, Bin):
        out = Bin(e.op, _map(e.a, fn), _map(e.b, fn))
        return fn(out) or out
    if isinstance(e, Pow):
        out = Pow(_map(e.base, fn), e.k)
        return fn(out) or out
    raise TypeError(f"unknown expression node {e!r}")


# ---------------------------------------------------------------- interpretations
def poly(refs, x: Indet) -> Expr:
    """Σ refs[i]·xⁱ (§1.3)."""
    out: Expr = Const(0)
    for i, r in enumerate(refs):
        term = _lift(r) if i == 0 else Bin("*", _lift(r), Pow(x, i))
        out = term if i == 0 else Bin("+", out, term)
    return out


def limbs(refs, bits: int) -> Expr:
    """Σ refs[i]·2^(bits·i), saturated or not (§1.3)."""
    out: Expr = Const(0)
    for i, r in enumerate(refs):
        term = _lift(r) if i == 0 else Bin("*", _lift(r), Const(1 << (bits * i)))
        out = term if i == 0 else Bin("+", out, term)
    return out


# ---------------------------------------------------------------- assertions
@dataclass
class RangeAssert:
    expr: Expr
    lo: Expr          # lo <= expr
    hi: Expr          # expr < hi
    source: str = ""

    def __str__(self): return f"{self.lo} <= {self.expr} < {self.hi}"


@dataclass
class AlgAssert:
    kind: str         # eq | eqmod
    lhs: Expr
    rhs: Expr
    mods: list = field(default_factory=list)

    def __str__(self):
        m = "" if not self.mods else " mod " + ", ".join(str(x) for x in self.mods)
        return f"{self.lhs} == {self.rhs}{m}"


_pending: list = []


def _cmp(a: Expr, op: str, b: Expr):
    c = _Cmp(a, op, b)
    return c


@dataclass
class _Cmp:
    a: Expr
    op: str
    b: Expr

    def __bool__(self):
        # Python evaluates `lo <= e < hi` as two comparisons joined by `and`, which
        # calls bool() on the first one. Record it so rng() sees both halves.
        _pending.append(self)
        return True


def rng(cmp_result) -> RangeAssert:
    """rng(lo <= e < hi) — also accepts a single comparison."""
    parts = _pending[:] + [cmp_result]
    _pending.clear()
    if len(parts) != 2:
        raise ValueError("rng is written rng(lo <= e < hi): both bounds are required")
    first, second = parts
    if first.b is not second.a:
        raise ValueError("rng(lo <= e < hi): the two comparisons must share the middle term")
    if first.op != "<=" or second.op != "<":
        raise ValueError("rng is written lo <= e < hi")
    return RangeAssert(second.a, first.a, second.b)


def abs_lt(e, b) -> RangeAssert:
    """|e| < b, i.e. −b < e < b."""
    _pending.clear()
    bound = _lift(b)
    return RangeAssert(_lift(e), Bin("-", Const(0), bound) + Const(1), bound)


def eq(a, b) -> AlgAssert:
    return AlgAssert("eq", _lift(a), _lift(b))


def eqmod(a, b, mods) -> AlgAssert:
    return AlgAssert("eqmod", _lift(a), _lift(b), [_lift(m) for m in mods])


# ---------------------------------------------------------------- target
@dataclass
class Array:
    ctype: str
    count: int


@dataclass
class ArgSpec:
    direction: str            # in | out | inout
    kind: object              # Array or ctype string


def In(kind): return ArgSpec("in", kind)
def Out(kind): return ArgSpec("out", kind)
def InOut(kind): return ArgSpec("inout", kind)


class ObjRef:
    """t.arg("r"): indexable for arrays, usable directly for scalars."""

    def __init__(self, name: str, count: int):
        self.name, self.count = name, count

    def __getitem__(self, i: int) -> Ref:
        if not 0 <= i < self.count:
            raise IndexError(f"{self.name}[{i}] out of range (count {self.count})")
        return Ref(self.name, i)

    def __iter__(self):
        return (self[i] for i in range(self.count))

    def _scalar(self) -> Ref:
        return Ref(self.name, 0)

    @property
    def entry(self): return self._scalar().entry

    @property
    def exit(self): return self._scalar().exit

    def at(self, point): return self._scalar().at(point)


@dataclass
class Cut:
    point: Point
    ranges: list = field(default_factory=list)
    algs: list = field(default_factory=list)

    def range(self, *items):
        self.ranges += _flatten(items)
        return self

    def alg(self, *items):
        self.algs += _flatten(items)
        return self


def _flatten(items):
    out = []
    for it in items:
        if isinstance(it, (RangeAssert, AlgAssert)):
            out.append(it)
        else:
            out += list(it)
    return out


class Target:
    def __init__(self, entry: str, args: dict[str, ArgSpec], returns=None):
        self.entry_name = entry
        self.args = args
        self.returns = returns
        self.pre_ranges: list = []
        self.pre_algs: list = []
        self.post_ranges: list = []
        self.post_algs: list = []
        self.cut_list: list[Cut] = []
        self.ghosts: dict[str, Expr] = {}
        self.ghost_order: list[str] = []

    # -------------------------------------------------------- references
    def arg(self, name: str) -> ObjRef:
        if name not in self.args:
            raise KeyError(f"{name} is not an argument of {self.entry_name}")
        kind = self.args[name].kind
        return ObjRef(name, kind.count if isinstance(kind, Array) else 1)

    def ghost(self, name: str, expr: Expr) -> Ghost:
        if name in self.ghosts:
            raise ValueError(f"ghost {name} is bound twice (S4)")
        self.ghosts[name] = expr
        self.ghost_order.append(name)
        return Ghost(name)

    # -------------------------------------------------------- assertions
    def pre(self, range=(), alg=()):
        self.pre_ranges += _flatten(range)
        self.pre_algs += _flatten(alg)

    def cut(self, tag: str, k: int) -> Cut:
        c = Cut(Point(CUT, tag, k))
        self.cut_list.append(c)
        return c

    def post(self, range=(), alg=(), same_as: Cut | None = None):
        if same_as is not None:
            self.post_ranges += [replace_time(a, same_as.point, EXIT_POINT) for a in same_as.ranges]
            self.post_algs += [replace_time(a, same_as.point, EXIT_POINT) for a in same_as.algs]
        self.post_ranges += _flatten(range)
        self.post_algs += _flatten(alg)

    # -------------------------------------------------------- views
    def points(self) -> list[Point]:
        return [ENTRY_POINT] + [c.point for c in self.cut_list] + [EXIT_POINT]

    def assertions_at(self, point: Point):
        """(range asserts, algebraic asserts) attached to this time point."""
        if point == ENTRY_POINT:
            return self.pre_ranges, self.pre_algs
        if point == EXIT_POINT:
            return self.post_ranges, self.post_algs
        for c in self.cut_list:
            if c.point == point:
                return c.ranges, c.algs
        raise KeyError(point)


def replace_time(assertion, old: Point, new: Point):
    """Copy an assertion with references moved from one time point to another."""
    def sub(e):
        return _map(e, lambda n: replace(n, time=new)
                    if isinstance(n, Ref) and n.time == old else None)
    if isinstance(assertion, RangeAssert):
        return RangeAssert(sub(assertion.expr), sub(assertion.lo), sub(assertion.hi),
                           assertion.source)
    return AlgAssert(assertion.kind, sub(assertion.lhs), sub(assertion.rhs),
                     [sub(m) for m in assertion.mods])
