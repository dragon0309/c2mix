"""Write the range VC (spec §7.4), the pure QF_BV file `z3` solves.

Premises: the range assertions at the start of the segment plus its bit-vector
statements. Goal: the range assertions at the end, the safety obligations of every
EXACT decision, and every hint the assembler found.

With --range-split=N the obligations are spread over N files, and every obligation
becomes its own query, sent with only its cone of influence (vc/prover.py): the
statements that define the symbols it mentions, transitively, and every premise that
touches them. A query proves its obligation from a subset of the segment's model, which
implies it holds in the whole model, and together the queries cover every obligation —
the same proof as one file, cut along the lines where it was independent anyway (one
NTT butterfly does not look at another). The queries in a file are separated by
`(reset)`; G5 requires every one of them to be unsat.

Asking one obligation at a time is not just tidier. z3 refutes the negated conjunction
of a single NTT butterfly's twelve obligations in 16 s, and each of the twelve alone
in under 0.2 s.
"""
from __future__ import annotations

from pathlib import Path

from ..mixfmt.writer import to_str
from ..vc import prover
from ..vc.assemble import VC


def _conj(terms):
    if not terms:
        return "true"
    out = terms[0]
    for t in terms[1:]:
        out = ["and", out, t]
    return out


def obligations(vc: VC) -> list:
    return list(vc.goal_range) + list(vc.seg.safety) + [h.bv_term() for h in vc.hints]


def depths(vc: VC) -> list:
    """The cone depth each obligation is sent with (None: the whole cone): what the
    assembler found for large cones, and what each hint was proved with."""
    out = [vc.depths.get(to_str(g)) for g in list(vc.goal_range) + list(vc.seg.safety)]
    return out + [getattr(h, "depth", None) for h in vc.hints]


def render(vc: VC) -> str:
    lines = ["(set-logic QF_BV)"]
    for name in sorted(vc.seg.decls):
        sort = vc.seg.decls[name]
        if isinstance(sort, list) and sort[:2] == ["_", "BitVec"]:
            lines.append(to_str(["declare-const", name, sort]))
    lines.append(to_str(["assert", _conj(vc.premise_range)]))
    for t in vc.seg.bv:
        if isinstance(t, list) and t[0] == "=" and vc.seg.decls.get(t[1]) == "Int":
            continue                       # Int aliases belong to the algebraic side
        lines.append(to_str(["assert", t]))
    lines.append(to_str(["assert", ["not", _conj(obligations(vc))]]))
    lines += ["(check-sat)", "(exit)"]
    return "\n".join(lines) + "\n"


def partition(vc: VC, parts: int) -> list[tuple[list, list[str], list[int], object]]:
    """([(obligation, its slice)], symbols, statement indices, model) for each of at most
    `parts` files.

    Obligations whose cones share a statement form one cluster (union–find); clusters
    are dealt out largest first to the file with the least work so far. Everything is
    ordered by first appearance, so the split is deterministic (M9)."""
    model = prover.RangeModel(vc.seg, vc.premise_range)
    goals = obligations(vc)
    cones = [model.cone(g, d) for g, d in zip(goals, depths(vc))]
    parent = list(range(len(goals)))

    def find(i: int) -> int:
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    owner: dict[int, int] = {}
    for i, (_, stmts) in enumerate(cones):
        for s in stmts:
            if s in owner:
                a, b = find(owner[s]), find(i)
                if a != b:
                    parent[max(a, b)] = min(a, b)
            else:
                owner[s] = i
    clusters: dict[int, list[int]] = {}
    for i in range(len(goals)):
        clusters.setdefault(find(i), []).append(i)

    def weight(members: list[int]) -> int:
        return len({s for i in members for s in cones[i][1]}) + len(members)

    ordered = sorted(clusters.values(), key=lambda m: (-weight(m), m[0]))
    bins: list[list[int]] = [[] for _ in range(max(1, min(parts, len(ordered))))]
    load = [0] * len(bins)
    for members in ordered:
        k = min(range(len(bins)), key=lambda j: (load[j], j))
        bins[k] += members
        load[k] += weight(members)
    out = []
    for members in bins:
        members.sort()
        names = sorted({n for i in members for n in cones[i][0]})
        stmts = sorted({s for i in members for s in cones[i][1]})
        out.append(([(goals[i], cones[i]) for i in members], names, stmts, model))
    return out


def render_part(goals: list, model) -> str:
    """One sliced query per obligation, separated by (reset)."""
    lines = []
    for k, (goal, (names, stmts)) in enumerate(goals):
        lines += ["(reset)"] if k else []
        lines.append("(set-logic QF_BV)")
        lines += [to_str(["declare-const", n, model.sorts[n]]) for n in names]
        lines += [model.text[i] for i in stmts]
        lines += [to_str(["assert", ["not", goal]]), "(check-sat)"]
    lines.append("(exit)")
    return "\n".join(lines) + "\n"


def write(vc: VC, path: str | Path, parts: int = 1) -> list[Path]:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    for old in path.parent.glob(path.name.replace(".smt2", ".*.smt2")):
        old.unlink()                       # parts from an earlier, wider split
    if parts <= 1 or not obligations(vc):
        path.write_text(render(vc), encoding="utf-8")
        return [path]
    if path.exists():
        path.unlink()
    out = []
    for i, (goals, names, stmts, model) in enumerate(partition(vc, parts)):
        p = path.with_suffix(f".{i}.smt2")
        p.write_text(render_part(goals, model), encoding="utf-8")
        out.append(p)
    return out
