"""Traces: the interface between the frontend and everything after it (spec §3).

A trace is the IR program plus the snapshots the specification can talk about: the
entry state, one per `c2mix_cut(tag)` execution, and the exit state (§5.5). A snapshot
maps each element of a registered object to the SSA value it holds at that moment.

Phase 3's executor produces these from LLVM IR; phase 2's tests build them by hand.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from .ops import Builder, Program, Value

ENTRY = "entry"
EXIT = "exit"
CUT = "cut"


@dataclass(frozen=True)
class ObjectInfo:
    """A registered object (§4.2): a scalar is count == 1."""
    name: str
    count: int
    width: int
    signed: bool


@dataclass(frozen=True)
class Point:
    """A time point: entry, exit, or the k-th execution of cut `tag`."""
    kind: str
    tag: str | None = None
    k: int | None = None

    def __str__(self) -> str:
        return self.kind if self.kind != CUT else f"cut({self.tag}, {self.k})"


ENTRY_POINT = Point(ENTRY)
EXIT_POINT = Point(EXIT)


@dataclass
class Snapshot:
    point: Point
    values: dict[tuple[str, int], Value]
    instr_index: int                      # where in prog.instrs this moment sits


@dataclass
class Trace:
    prog: Program
    objects: dict[str, ObjectInfo] = field(default_factory=dict)
    snapshots: list[Snapshot] = field(default_factory=list)
    origins: dict = field(default_factory=dict)
    """SSA name -> where it came from: a registered object and index, or the LLVM value
    and source line that produced it. The frontend fills this in; §7.5's symbol table
    is what reads it."""

    def at(self, point: Point) -> Snapshot:
        for s in self.snapshots:
            if s.point == point:
                return s
        raise KeyError(f"no snapshot for {point}")

    def cuts(self) -> list[Point]:
        return [s.point for s in self.snapshots if s.point.kind == CUT]

    def value(self, point: Point, obj: str, idx: int = 0) -> Value:
        snap = self.at(point)
        if (obj, idx) not in snap.values:
            raise KeyError(f"{obj}[{idx}] is not live at {point}")
        return snap.values[(obj, idx)]


class TraceBuilder:
    """Hand-build a trace: register objects, mark cuts, finish with done().
    Phase 2 uses this instead of the C frontend."""

    def __init__(self):
        self.b = Builder()
        self.objects: dict[str, ObjectInfo] = {}
        self.state: dict[tuple[str, int], Value] = {}
        self.snapshots: list[Snapshot] = []
        self._entry_taken = False

    def input(self, name: str, width: int, signed: bool, count: int = 1) -> list[Value]:
        """Register an object and make its elements symbolic inputs."""
        self.objects[name] = ObjectInfo(name, count, width, signed)
        vals = []
        for i in range(count):
            v = self.b.input(f"{name}_{i:0{len(str(count - 1))}d}" if count > 1 else name,
                             width, signed)
            self.state[(name, i)] = v
            vals.append(v)
        return vals

    def register(self, name: str, values: list[Value]) -> None:
        """Register an object whose elements are already computed values (outputs)."""
        v0 = values[0]
        self.objects[name] = ObjectInfo(name, len(values), v0.width, v0.signed)
        for i, v in enumerate(values):
            self.state[(name, i)] = v

    def store(self, name: str, idx: int, value: Value) -> None:
        self.state[(name, idx)] = value

    def entry(self) -> None:
        self._snapshot(ENTRY_POINT)
        self._entry_taken = True

    def cut(self, tag: str, k: int) -> Point:
        self.b.marker(f"{tag}#{k}")
        p = Point(CUT, tag, k)
        self._snapshot(p)
        return p

    def done(self) -> Trace:
        self._snapshot(EXIT_POINT)
        return Trace(self.b.build(), dict(self.objects), list(self.snapshots))

    def _snapshot(self, point: Point) -> None:
        self.snapshots.append(Snapshot(point, dict(self.state), len(self.b.prog.instrs)))
