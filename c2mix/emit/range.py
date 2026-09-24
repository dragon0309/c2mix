"""Write the range VC (spec §7.4), the pure QF_BV file `z3` solves.

Premises: the range assertions at the start of the segment plus its bit-vector
statements. Goal: the range assertions at the end, the safety obligations of every
EXACT decision, and every hint the assembler found.
"""
from __future__ import annotations

from pathlib import Path

from ..mixfmt.writer import to_str
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


def render(vc: VC, part: int = 0, parts: int = 1) -> str:
    """With parts > 1 the obligations are split across files (--range-split): each
    coefficient's bound is independent, so proving them separately is the same proof."""
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
    want = obligations(vc)[part::parts]
    lines.append(to_str(["assert", ["not", _conj(want)]]))
    lines += ["(check-sat)", "(exit)"]
    return "\n".join(lines) + "\n"


def write(vc: VC, path: str | Path, parts: int = 1) -> list[Path]:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    if parts == 1:
        path.write_text(render(vc), encoding="utf-8")
        return [path]
    out = []
    for i in range(parts):
        p = path.with_suffix(f".{i}.smt2")
        p.write_text(render(vc, i, parts), encoding="utf-8")
        out.append(p)
    return out
