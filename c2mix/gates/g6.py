"""G6 — every mix VC is unsat, solved with extend_z3's bin/main (§10.2 flags)."""
from __future__ import annotations

from pathlib import Path

from ..oracle import run_mix


def check(paths, cfg, log_dir, prepass: bool | None = None, use_systemd: bool = True,
          timeout: float | None = 1800) -> tuple[list[str], list]:
    """`unsat` is the only pass. A `sat` means "not proved", not "the VC is false":
    the same file can come back sat without the partition prepass and unsat with it
    (F10), so a sat has to be classified with G3/G4 before blaming the program."""
    prepass = cfg.prepass_default if prepass is None else prepass
    bad, results = [], []
    for p in paths:
        r = run_mix(cfg, p, prepass, log_dir, use_systemd=use_systemd, timeout=timeout)
        results.append(r)
        if r.result != "unsat":
            bad.append(f"{Path(p).name}: {r.result} (log {r.log})")
    return bad, results
