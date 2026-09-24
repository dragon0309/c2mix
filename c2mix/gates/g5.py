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
    got = out.strip().splitlines()[-1].strip() if out.strip() else "no-output"
    return got == "unsat", got


def check(paths, z3_bin: str = "z3", timeout: float = 600) -> list[str]:
    bad = []
    for p in paths:
        ok, got = check_file(p, z3_bin, timeout)
        if not ok:
            bad.append(f"{Path(p).name}: {got}")
    return bad
