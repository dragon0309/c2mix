"""Write the five-section mix VC (spec §7.3), the file `bin/main` solves."""
from __future__ import annotations

from pathlib import Path

from ..mixfmt.reader import SECTION_COMMENTS
from ..mixfmt.writer import to_str
from ..vc.assemble import VC

TRUE = "true"


def _conj(terms):
    if not terms:
        return TRUE
    out = terms[0]
    for t in terms[1:]:
        out = ["and", out, t]
    return out


def render(vc: VC, hints_mode: str = "omit") -> str:
    lines = ["(set-info :smt-lib-version 2.0)", "(set-logic ALL)", SECTION_COMMENTS[0]]
    for name in sorted(vc.seg.decls):
        lines.append(to_str(["declare-const", name, vc.seg.decls[name]]))

    lines.append(SECTION_COMMENTS[1])
    lines.append(to_str(["assert", _conj(vc.premise_range)]))
    for t in vc.seg.bv:
        lines.append(to_str(["assert", t]))
    if hints_mode == "emit":
        # CryptoLine writes the range half of a hint as a placeholder; the obligation
        # itself lives in the range VC (§6.4).
        lines += [to_str(["assert", TRUE]) for _ in vc.hints]

    lines.append(SECTION_COMMENTS[2])
    lines.append(to_str(["assert", _conj(vc.premise_alg)]))
    for t in vc.ghost_bindings:
        lines.append(to_str(["assert", t]))
    for t in vc.seg.alg:
        lines.append(to_str(["assert", t]))
    if hints_mode == "emit":
        for h in vc.hints:
            lines.append(to_str(["assert", h.poly_term(vc.enc)]))

    lines.append(SECTION_COMMENTS[3])
    goal = vc.goal_alg if vc.goal_alg else [TRUE, TRUE]      # M6: trivial goals are explicit
    lines.append(to_str(["assert", ["not", ["and"] + goal]]))
    lines += [SECTION_COMMENTS[4], "(check-sat)", "(exit)"]
    return "\n".join(lines) + "\n"


def write(vc: VC, path: str | Path, hints_mode: str = "omit") -> Path:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(render(vc, hints_mode), encoding="utf-8")
    return path
