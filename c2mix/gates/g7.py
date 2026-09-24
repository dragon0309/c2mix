"""G7 — mutation testing: the gates must have teeth (spec §8.1).

Each mutation makes the program (or the specification) wrong in one small way; some
gate has to notice. A mutation that no gate notices is either a hole in the gates or an
equivalent mutation, and then it needs a written reason (`target.toml`, §8.1).
"""
from __future__ import annotations

import re
from dataclasses import dataclass, replace
from typing import Callable

from ..ir.ops import Instr, Program
from ..ir.trace import Trace


@dataclass
class Mutant:
    name: str
    trace: Trace
    description: str


def _rebuild(trace: Trace, instrs: list[Instr]) -> Trace:
    prog = Program(list(trace.prog.inputs), instrs)
    return Trace(prog, dict(trace.objects), list(trace.snapshots))


def spec_refs(target) -> set:
    """(point, object, index) triples the specification reads. Mutating anything else
    cannot change what is being proved, so it would be an equivalent mutation."""
    out = set()
    for point in target.points():
        ranges, algs = target.assertions_at(point)
        for a in list(ranges) + list(algs):
            exprs = ([a.expr, a.lo, a.hi] if hasattr(a, "expr") else
                     [a.lhs, a.rhs] + list(a.mods))
            for e in exprs:
                for r in e.refs():
                    out.add((str(r.time), r.obj, r.idx))
    for e in target.ghosts.values():
        for r in e.refs():
            out.add((str(r.time), r.obj, r.idx))
    return out


def mutate(trace: Trace, limit: int = 10, refs: set | None = None) -> list[Mutant]:
    """Up to `limit` mutants, spread evenly over the kinds §8.1 lists rather than
    exhausting the first kind. Within a kind the picks are spread over the program,
    so a mutant is not always in the first butterfly. `refs` (from spec_refs) keeps
    index mutations on elements the specification actually reads."""
    kinds = [make(trace) for make in
             (_const_off_by_one, _swap_add_sub, _swap_operands, _shift_off_by_one,
              _substitute_operand, lambda t: _index_off_by_one(t, refs))]
    kinds = [k for k in kinds if k]
    if not kinds:
        return []
    per_kind = max(1, -(-limit // len(kinds)))
    spread = [k[::max(1, len(k) // per_kind)] for k in kinds]
    out: list[Mutant] = []
    for i in range(max(len(s) for s in spread)):
        for s in spread:
            if i < len(s) and len(out) < limit:
                out.append(s[i])
    return out[:limit]


def _used(trace: Trace, name: str) -> bool:
    """Is this value read by an instruction or visible in a snapshot?"""
    if any(name == a.name for ins in trace.prog.instrs for a in ins.args):
        return True
    return any(v.name == name for s in trace.snapshots for v in s.values.values())


def _const_off_by_one(trace: Trace) -> list[Mutant]:
    out = []
    for i, ins in enumerate(trace.prog.instrs):
        if ins.op == "const" and _used(trace, ins.result.name):
            instrs = list(trace.prog.instrs)
            instrs[i] = replace(ins, value=ins.value + 1)
            out.append(Mutant(f"const+1@{i}", _rebuild(trace, instrs),
                              f"constant {ins.value} -> {ins.value + 1}"))
    return out


def _swap_add_sub(trace: Trace) -> list[Mutant]:
    out = []
    for i, ins in enumerate(trace.prog.instrs):
        if ins.op in ("add", "sub") and _used(trace, ins.result.name):
            other = "sub" if ins.op == "add" else "add"
            instrs = list(trace.prog.instrs)
            instrs[i] = replace(ins, op=other)
            out.append(Mutant(f"{ins.op}->{other}@{i}", _rebuild(trace, instrs),
                              f"{ins.op} becomes {other}"))
    return out


def _swap_operands(trace: Trace) -> list[Mutant]:
    out = []
    for i, ins in enumerate(trace.prog.instrs):
        if ins.op in ("sub",) and len(ins.args) == 2 and ins.args[0] != ins.args[1]:
            instrs = list(trace.prog.instrs)
            instrs[i] = replace(ins, args=(ins.args[1], ins.args[0]))
            out.append(Mutant(f"swap@{i}", _rebuild(trace, instrs), "operands swapped"))
    return out


def _shift_off_by_one(trace: Trace) -> list[Mutant]:
    out = []
    for i, ins in enumerate(trace.prog.instrs):
        if ins.op in ("shl", "ashr", "lshr") and 0 < ins.k < ins.args[0].width - 1:
            instrs = list(trace.prog.instrs)
            instrs[i] = replace(ins, k=ins.k + 1)
            out.append(Mutant(f"shift+1@{i}", _rebuild(trace, instrs),
                              f"shift {ins.k} -> {ins.k + 1}"))
    return out


def _substitute_operand(trace: Trace) -> list[Mutant]:
    """Drop a statement: everything downstream reads its first operand instead."""
    out = []
    for i, ins in enumerate(trace.prog.instrs):
        if ins.result is None or not ins.args:
            continue
        src = ins.args[0]
        if src.width != ins.result.width or src.signed != ins.result.signed:
            continue
        instrs = list(trace.prog.instrs)
        for j in range(i + 1, len(instrs)):
            nxt = instrs[j]
            if any(a.name == ins.result.name for a in nxt.args):
                instrs[j] = replace(nxt, args=tuple(src if a.name == ins.result.name else a
                                                    for a in nxt.args))
        snaps = [replace(s, values={k: (src if v.name == ins.result.name else v)
                                    for k, v in s.values.items()}) for s in trace.snapshots]
        t = _rebuild(trace, instrs)
        t.snapshots = snaps
        out.append(Mutant(f"drop@{i}", t, f"{ins.op} dropped, uses read {src.name}"))
    return out


def _index_off_by_one(trace: Trace, refs: set | None = None) -> list[Mutant]:
    """Read the neighbouring array element at a snapshot."""
    out = []
    for si, snap in enumerate(trace.snapshots):
        for (obj, idx), v in list(snap.values.items()):
            nxt = snap.values.get((obj, idx + 1))
            if nxt is None or nxt.name == v.name:
                continue
            if refs is not None and (str(snap.point), obj, idx) not in refs:
                continue
            snaps = list(trace.snapshots)
            values = dict(snap.values)
            values[(obj, idx)] = nxt
            snaps[si] = replace(snap, values=values)
            t = _rebuild(trace, list(trace.prog.instrs))
            t.snapshots = snaps
            out.append(Mutant(f"index+1@{snap.point}.{obj}[{idx}]", t,
                              f"{obj}[{idx}] reads {obj}[{idx + 1}]"))
            break
    return out


def kill_report(mutant: Mutant, gates: list[tuple[str, Callable[[Trace], bool]]]) -> str | None:
    """The first gate that notices, or None if the mutant survives."""
    for name, gate in gates:
        try:
            if not gate(mutant.trace):
                return name
        except Exception as e:                    # a mutant that breaks the build is caught too
            return f"{name} ({type(e).__name__}: {str(e)[:60]})"
    return None


# ------------------------------------------------------------------ C mutations
@dataclass
class SourceMutant:
    name: str
    path: str                 # file inside the target's work copy
    text: str                 # the whole file, mutated
    description: str


_COMMENT = re.compile(r"/\*.*?\*/|//[^\n]*", re.S)
_TOKEN = re.compile(r"""
      (?P<num>\b\d+\b)
    | (?P<op>\+\+|--|<<|>>|[-+*<>])
    | (?P<index>\[\s*[A-Za-z_][A-Za-z_0-9]*\s*\])
""", re.X)


def _maskable(text: str) -> list[bool]:
    """Positions that may be mutated: not inside a comment, a preprocessor line or a
    string literal. Mutating those changes nothing or breaks the build for the wrong
    reason, and a mutant has to be wrong in exactly one interesting way."""
    ok = [True] * len(text)
    for m in _COMMENT.finditer(text):
        for i in range(m.start(), m.end()):
            ok[i] = False
    pos = 0
    for line in text.splitlines(keepends=True):
        if line.lstrip().startswith("#"):
            for i in range(pos, pos + len(line)):
                ok[i] = False
        pos += len(line)
    in_str, i = None, 0
    while i < len(text):
        if not ok[i] and in_str is None:
            i += 1                 # already masked: an apostrophe in a comment is prose
            continue
        c = text[i]
        if in_str:
            ok[i] = False
            if c == "\\":
                i += 2
                continue
            if c == in_str:
                in_str = None
        elif c in "\"'":
            in_str, ok[i] = c, False
        i += 1
    return ok


FUNC_HEAD = re.compile(r"^[A-Za-z_][\w \t*]*\b(\w+)\s*\([^;]*$")


def function_lines(text: str, names: set) -> set:
    """The lines of the functions in `names`. A mutation anywhere else cannot change
    what this target executes, so it would be equivalent by construction; G7 is about
    whether the gates have teeth, not about how much dead code a file contains."""
    lines = text.splitlines()
    out, i = set(), 0
    while i < len(lines):
        m = FUNC_HEAD.match(lines[i].strip())
        if not m:
            i += 1
            continue
        name = m.group(1)
        start, depth, seen = i, 0, False
        while i < len(lines):
            depth += lines[i].count("{") - lines[i].count("}")
            seen |= "{" in lines[i]
            i += 1
            if seen and depth <= 0:
                break
        if any(name == n or n.endswith("_" + name) for n in names):
            out |= set(range(start + 1, i + 1))
    return out


def mutate_source(text: str, path: str, limit: int = 24,
                  lines_allowed: set | None = None) -> list[SourceMutant]:
    """The mutation kinds §8.1 lists, applied to C rather than to the trace: a constant
    off by one, `+` and `−` exchanged, a shift the wrong way, a comparison loosened,
    an index off by one, and a statement deleted."""
    ok = _maskable(text)
    if lines_allowed is not None:
        pos = 0
        for n, line in enumerate(text.splitlines(keepends=True), start=1):
            if n not in lines_allowed:
                for i in range(pos, min(pos + len(line), len(ok))):
                    ok[i] = False
            pos += len(line)
    kinds: dict[str, list[SourceMutant]] = {}

    def add(kind, name, new, why):
        kinds.setdefault(kind, []).append(SourceMutant(name, path, new, why))

    for m in _TOKEN.finditer(text):
        if not all(ok[i] for i in range(m.start(), m.end())):
            continue
        s, e = m.span()
        if m.lastgroup == "num":
            v = int(m.group())
            add("const", f"const+1@{s}", text[:s] + str(v + 1) + text[e:],
                f"constant {v} -> {v + 1}")
        elif m.lastgroup == "op":
            swap = {"+": "-", "-": "+", "<<": ">>", ">>": "<<", "<": "<=", ">": ">="}
            tok = m.group()
            if tok in swap:
                add(f"op{tok}", f"{tok}->{swap[tok]}@{s}",
                    text[:s] + swap[tok] + text[e:], f"{tok} becomes {swap[tok]}")
        elif m.lastgroup == "index":
            inner = m.group()[1:-1].strip()
            add("index", f"index+1@{s}", text[:s] + f"[{inner} + 1]" + text[e:],
                f"[{inner}] -> [{inner} + 1]")

    lines = text.splitlines(keepends=True)
    pos = 0
    for n, line in enumerate(lines):
        body = line.strip()
        if body.endswith(";") and pos < len(ok) and ok[pos] and "return" not in body \
                and "c2mix_" not in body \
                and not body.startswith(("int", "uint", "const", "static", "struct")):
            add("delete", f"delete@{n + 1}", "".join(lines[:n] + lines[n + 1:]),
                f"statement deleted: {body[:40]}")
        pos += len(line)

    out: list[SourceMutant] = []
    order = [k for k in kinds if kinds[k]]
    per = max(1, -(-limit // max(1, len(order))))
    spread = {k: kinds[k][::max(1, len(kinds[k]) // per)] for k in order}
    for i in range(max((len(v) for v in spread.values()), default=0)):
        for k in order:
            if i < len(spread[k]) and len(out) < limit:
                out.append(spread[k][i])
    return out[:limit]
