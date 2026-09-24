"""G1 — the format contract, checked with `c2mix lint` (spec §8.1, §7.3, §7.4).

`cutN.smt2` is the five-section mix format, and the consumer profile is the one that
matters: it is what `bin/main` will accept. `cutN.range.smt2` is a plain QF_BV file
(§7.4) and has its own, much shorter contract, checked here.

Anything c2mix emits has to pass with zero errors; warnings are reported so a change
in shape is visible without failing the gate.
"""
from __future__ import annotations

import subprocess
from pathlib import Path

from ..mixfmt import lint

RANGE_SUFFIX = ".range.smt2"


def check(paths, profile: str = "consumer", cfg=None) -> tuple[list[str], dict]:
    """(errors, warning counts). Empty errors means the gate passes."""
    errors, warnings = [], {}
    z3 = (cfg.data["solver"]["range"]["bin"] if cfg else "z3")
    for p in paths:
        p = Path(p)
        if is_range_file(p):
            errors += check_range(p, z3)
            continue
        diags = lint.lint_file(p, profile, cfg, display=str(p))
        for d in diags:
            if d.severity == lint.E:
                errors.append(f"{p.name}: {d.render()}")
        for rule, n in lint.summarize(diags).items():
            warnings[rule] = warnings.get(rule, 0) + n
    return errors, warnings


def is_range_file(path: Path) -> bool:
    name = path.name
    return name.endswith(RANGE_SUFFIX) or ".range." in name


def check_range(path: Path, z3_bin: str = "z3") -> list[str]:
    """§7.4: `(set-logic QF_BV)`, declarations, premises, one negated goal, check-sat —
    and z3 has to be able to parse it."""
    text = path.read_text(encoding="utf-8")
    lines = [l.strip() for l in text.splitlines() if l.strip()]
    bad = []
    if not lines or lines[0] != "(set-logic QF_BV)":
        bad.append(f"{path.name}:1: E-RANGE-LOGIC the first line must be '(set-logic QF_BV)'")
    if "(check-sat)" not in lines:
        bad.append(f"{path.name}: E-RANGE-CHECK no (check-sat)")
    if not any(l.startswith("(assert (not ") for l in lines):
        bad.append(f"{path.name}: E-RANGE-GOAL no negated goal")
    if "Poly" in text or "eqP" in text:
        bad.append(f"{path.name}: E-RANGE-THEORY a range VC is pure QF_BV")
    p = subprocess.run([z3_bin, "-smt2", str(path)], capture_output=True, text=True)
    if "(error" in p.stdout + p.stderr:
        first = next(l for l in (p.stdout + p.stderr).splitlines() if "(error" in l)
        bad.append(f"{path.name}: E-RANGE-PARSE z3: {first[:120]}")
    return bad
