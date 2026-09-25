"""G5 — every range VC is unsat (safety, bounds and hints), solved with z3."""
from __future__ import annotations

import subprocess
from pathlib import Path


def check_file(path: str | Path, z3_bin: str = "z3", timeout: float = 600) -> tuple[bool, str]:
    try:
        p = subprocess.run([z3_bin, "-smt2", str(path)], capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return False, "timeout"
    out = p.stdout + p.stderr
    if "(error" in out:
        return False, "error: " + next(l for l in out.splitlines() if "(error" in l)[:120]
    # A split range VC holds one query per obligation (emit/range.py): every one of
    # them has to answer, and every answer has to be unsat.
    answers = [l.strip() for l in p.stdout.splitlines() if l.strip()]
    asked = Path(path).read_text().count("(check-sat)")
    if not answers:
        return False, "no-output"
    if len(answers) != asked:
        return False, f"{len(answers)} answer(s) to {asked} quer(ies)"
    bad = [a for a in answers if a != "unsat"]
    if bad:
        return False, bad[0] if asked == 1 else f"{len(bad)}/{asked} not unsat ({bad[0]})"
    return True, "unsat" if asked == 1 else f"unsat ×{asked}"


def check(paths, z3_bin: str = "z3", timeout: float = 600) -> list[str]:
    bad = []
    for p in paths:
        ok, got = check_file(p, z3_bin, timeout)
        if not ok:
            bad.append(f"{Path(p).name}: {got}")
    return bad
