"""Calls the external oracles through their CLIs (D2): extend_z3 `bin/main` and z3."""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

from .config import Config, ROOT

_RESULT = re.compile(r"Verification result:\s*\[([^\]]*)\]\s*([0-9.]+) seconds")
_RSS = re.compile(r"MaxRSS:\s*self=(\d+) KiB, gb-worker-max=(\d+) KiB")


@dataclass
class MixRun:
    file: str
    result: str             # unsat / sat / unknown / missing / timeout
    exit_code: int
    solver_seconds: float | None
    wall_seconds: float
    maxrss_kib: int | None  # max(self, gb-worker-max) as reported by bin/main
    log: str


def run_mix(cfg: Config, smt2: str | Path, prepass: bool, log_dir: str | Path,
            use_systemd: bool = True, timeout: float | None = None) -> MixRun:
    """Run bin/main on one file. bin/main writes run.log into its cwd, so every run
    gets its own working directory under log_dir (never inside extend_z3)."""
    smt2 = Path(smt2).resolve()
    log_dir = Path(log_dir)
    log_dir.mkdir(parents=True, exist_ok=True)
    cwd = Path(tempfile.mkdtemp(prefix=smt2.stem + ".", dir=log_dir))
    mix = cfg.data["solver"]["mix"]
    cmd = [str(cfg.path(mix["bin"])), str(smt2)] + cfg.mix_flags(prepass)
    if use_systemd and shutil.which("systemd-run"):
        cmd = ["systemd-run", "--user", "--scope", "--quiet",
               "-p", f"MemoryMax={mix['memory']}", "-p", "MemorySwapMax=0"] + cmd
    t0 = time.monotonic()
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        out, code = p.stdout + p.stderr, p.returncode
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        code = -1
    wall = time.monotonic() - t0
    log = cwd / "stdout.log"
    log.write_text(" ".join(cmd) + "\n" + out)
    m = _RESULT.findall(out)
    rss = _RSS.findall(out)
    result = m[-1][0] if m else ("timeout" if code == -1 else "missing")
    return MixRun(str(smt2), result, code, float(m[-1][1]) if m else None, wall,
                  max(int(rss[-1][0]), int(rss[-1][1])) if rss else None, str(log))


_Z3_ERR = re.compile(r'\(error "line (\d+) column \d+: (.*)"\)$')


def inject_prelude(raw: str) -> tuple[str, int, int]:
    """Same text transformation as extend_z3's inject_poly_prelude_if_missing.
    Returns (script, line after which the prelude starts, prelude line count)."""
    from .mixfmt.prelude import POLY_PRELUDE
    if "(declare-datatype Poly" in raw or ("(declare-datatypes" in raw and "Poly" in raw):
        return raw, 0, 0
    pos = raw.find("(set-logic")
    n = POLY_PRELUDE.count("\n") + 1
    if pos < 0:
        return POLY_PRELUDE + "\n" + raw, 0, n
    end = raw.find("\n", pos)
    if end < 0:
        return raw + "\n" + POLY_PRELUDE, raw.count("\n") + 1, n
    return raw[:end + 1] + POLY_PRELUDE + "\n" + raw[end + 1:], raw.count("\n", 0, end) + 1, n


def z3_parse_errors(cfg: Config, raw: str) -> list[tuple[int | None, str]]:
    """Parse a file with z3 exactly as extend_z3 sees it, without solving
    (check-sat is removed; it never spans lines, so line numbers are kept).
    Returns (source line, message) pairs."""
    script, after, n = inject_prelude(raw.replace("(check-sat)", ""))
    z3 = cfg.data["solver"]["range"]["bin"]
    p = subprocess.run([z3, "-in", "-smt2"], input=script, capture_output=True, text=True)
    out = []
    for ln in p.stdout.splitlines():
        m = _Z3_ERR.match(ln)
        if m:
            k = int(m.group(1))
            src = k if k <= after else (k - n if k > after + n else None)
            out.append((src, m.group(2)))
        elif ln.startswith("(error"):
            out.append((None, ln))
    return out
