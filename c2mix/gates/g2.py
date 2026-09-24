"""G2 — frontend fidelity: the trace means what the C program means (spec §8.1).

Differential execution. The native binary is built from the *same* `program.m2r.ll`
the executor read, with the same clang and the same `-fwrapv`, and linked against
`runtime/c2mix_rt.c`; so what is being compared is one IR, executed two ways. For each
test vector both sides produce the snapshot at every cut and at the exit, and every
element of every registered object has to agree.

Inputs are not restricted by the precondition (§8.1): the executor has to be faithful
everywhere, not only where the specification is interested.

Building the native side a second time at -O2 and comparing the two says whether the
program leans on undefined or implementation-defined behaviour (`W-UB-SENSITIVE`).
"""
from __future__ import annotations

import json
import random
import re
import subprocess
from dataclasses import dataclass, field
from pathlib import Path

from ..ir import interp
from ..ir.trace import CUT, ENTRY_POINT, EXIT_POINT, Point, Trace

EXHAUSTIVE_BITS = 24            # §8.1: enumerate every input below this many bits
TAG, K = "\0tag", "\0k"         # a dump's own keys, kept apart from object names
W_UB_SENSITIVE = "W-UB-SENSITIVE"


@dataclass
class Report:
    vectors: int = 0
    exhaustive: bool = False
    mismatches: list = field(default_factory=list)
    warnings: list = field(default_factory=list)
    compared: int = 0           # snapshot elements compared

    @property
    def ok(self) -> bool:
        return not self.mismatches


def input_objects(trace: Trace) -> dict:
    """{object name: {index: SSA value name}} for the objects `c2mix_input` made
    symbolic — read off the entry snapshot, so it cannot drift from the trace."""
    out: dict[str, dict[int, str]] = {}
    for (obj, i), v in trace.at(ENTRY_POINT).values.items():
        if v.kind == "input":
            out.setdefault(obj, {})[i] = v.name
    return out


def input_bits(trace: Trace) -> int:
    return sum(trace.objects[name].width * len(cells)
               for name, cells in input_objects(trace).items())


def vectors(trace: Trace, count: int, seed: int = 0,
            exhaustive_bits: int = EXHAUSTIVE_BITS) -> tuple[list[dict], bool]:
    """Test vectors as {object: [element values]}, read as the object's signedness."""
    objs = input_objects(trace)
    shape = [(name, i, trace.objects[name].width, trace.objects[name].signed)
             for name in objs for i in sorted(objs[name])]
    bits = sum(w for _, _, w, _ in shape)
    if bits <= exhaustive_bits:
        return _enumerate(shape), True
    rng = random.Random(seed)
    out = [_vector(shape, [_edge(rng, w, s) for _, _, w, s in shape])]
    for pattern in _boundary_patterns(shape):
        out.append(_vector(shape, pattern))
    while len(out) < count:
        out.append(_vector(shape, [rng.randint(*_span(w, s)) for _, _, w, s in shape]))
    return out[:max(count, len(out))], False


def _span(width: int, signed: bool) -> tuple[int, int]:
    return (-(1 << (width - 1)), (1 << (width - 1)) - 1) if signed else (0, (1 << width) - 1)


def _edges(width: int, signed: bool) -> list[int]:
    lo, hi = _span(width, signed)
    return sorted({lo, lo + 1, -1 if signed else 0, 0, 1, hi - 1, hi})


def _edge(rng: random.Random, width: int, signed: bool) -> int:
    return rng.choice(_edges(width, signed))


def _boundary_patterns(shape) -> list:
    """Every element at the same extreme, plus alternating extremes: the patterns
    §9's A4.1 asks for, and cheap enough to always include."""
    out = []
    per = [_edges(w, s) for _, _, w, s in shape]
    for k in range(max((len(p) for p in per), default=0)):
        out.append([p[k % len(p)] for p in per])
        out.append([p[(k + i) % len(p)] for i, p in enumerate(per)])
    return out


def _vector(shape, values) -> dict:
    out: dict[str, list[int]] = {}
    for (name, i, _, _), v in zip(shape, values):
        out.setdefault(name, []).append(v)
    return out


def _enumerate(shape) -> list[dict]:
    out, total = [], 1
    for _, _, w, _ in shape:
        total <<= w
    for n in range(total):
        values, rest = [], n
        for _, _, w, s in shape:
            pattern = rest & ((1 << w) - 1)
            rest >>= w
            values.append(interp.interpret(pattern, w, s))
        out.append(_vector(shape, values))
    return out


# --------------------------------------------------------------------- both sides
def trace_snapshots(trace: Trace, vector: dict) -> list[tuple[str, int, dict]]:
    """What the executor's trace says, as (tag, k, {(object, index): value})."""
    values = {}
    for name, cells in input_objects(trace).items():
        for i, vname in cells.items():
            values[vname] = vector[name][i]
    patterns = interp.run(trace.prog, values)
    out = []
    for snap in trace.snapshots:
        if snap.point == ENTRY_POINT:
            continue
        got = {}
        for (obj, i), v in snap.values.items():
            info = trace.objects[obj]
            got[(obj, i)] = interp.interpret(patterns[v.name] & ((1 << info.width) - 1),
                                             info.width, info.signed)
        tag = "exit" if snap.point == EXIT_POINT else snap.point.tag
        out.append((tag, snap.point.k or 0, got))
    return out


def native_run(binary: Path, vecs: list[dict], work: Path, timeout: float = 600) -> list[list]:
    """Run the native binary over every vector; one dump group per vector."""
    work.mkdir(parents=True, exist_ok=True)
    inp, outp = work / "vectors.jsonl", work / "dumps.jsonl"
    inp.write_text("".join(json.dumps(v) + "\n" for v in vecs))
    subprocess.run([str(binary)], check=True, timeout=timeout,
                   env={"C2MIX_INPUT": str(inp), "C2MIX_OUTPUT": str(outp), "PATH": "/usr/bin"})
    groups, current = [], []
    for line in outp.read_text().splitlines():
        row = _parse_dump(line)
        current.append(row)
        if row[TAG] == "exit":
            groups.append(current)
            current = []
    if current:
        groups.append(current)
    return groups


def _parse_dump(line: str) -> dict:
    """A dump line is `{"tag": …, "k": …, <object>: […], …}` (§4.2). An object may
    itself be called `tag` or `k`, so the two metadata keys are taken by position —
    the runtime always writes them first — and the objects keep their own names."""
    pairs = json.loads(line, object_pairs_hook=list)
    (_, tag), (_, k) = pairs[0], pairs[1]
    row = {TAG: tag, K: k}
    row.update({name: value for name, value in pairs[2:]})
    return row


def check(trace: Trace, binary: Path, vecs: list[dict], work: Path,
          timeout: float = 600) -> Report:
    rep = Report(vectors=len(vecs))
    groups = native_run(binary, vecs, work, timeout)
    if len(groups) != len(vecs):
        rep.mismatches.append(f"the native run produced {len(groups)} results "
                              f"for {len(vecs)} vectors")
        return rep
    for vec, group in zip(vecs, groups):
        ours = trace_snapshots(trace, vec)
        if len(ours) != len(group):
            rep.mismatches.append(f"{vec}: {len(ours)} snapshots in the trace, "
                                  f"{len(group)} natively")
            break
        for (tag, k, got), row in zip(ours, group):
            if (tag, k) != (row[TAG], row[K]):
                rep.mismatches.append(
                    f"{vec}: cut ({tag}, {k}) vs ({row[TAG]}, {row[K]})")
                break
            for (obj, i), value in sorted(got.items()):
                native = row[obj][i]
                rep.compared += 1
                if value != native:
                    rep.mismatches.append(
                        f"{vec}: at ({tag}, {k}) {obj}[{i}] is {value} in the trace, "
                        f"{native} natively")
            if rep.mismatches:
                break
        if rep.mismatches:
            break
    return rep


def ub_sensitive(o0: Path, o2: Path, vecs: list[dict], work: Path) -> list[str]:
    """`W-UB-SENSITIVE`: -O0 and -O2 disagree, so the program depends on UB."""
    a = native_run(o0, vecs, work / "o0")
    b = native_run(o2, vecs, work / "o2")
    if a != b:
        for vec, x, y in zip(vecs, a, b):
            if x != y:
                return [f"{W_UB_SENSITIVE}: -O0 and -O2 differ on {vec}"]
    return []
