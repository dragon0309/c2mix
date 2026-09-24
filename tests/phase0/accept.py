#!/usr/bin/env python3
"""Phase 0 acceptance (spec §9, 第 0 階段): A0.1–A0.3 as gates, A0.4 summarized.

Writes reports/accept-0-<date>.md. Exit status 0 only if every gate passes.

usage: tests/phase0/accept.py [--no-solve] [--no-systemd]
"""
from __future__ import annotations

import argparse
import datetime
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from c2mix import config  # noqa: E402
from c2mix.mixfmt import lint  # noqa: E402

G10 = r"kyber|dilithium|saber|mceliece|p256|25519|3329|8380417"


def run(cmd: list[str], log: Path) -> tuple[int, float, str]:
    t0 = time.monotonic()
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    dt = time.monotonic() - t0
    out = p.stdout + p.stderr
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text("$ " + " ".join(cmd) + "\n" + out)
    return p.returncode, dt, out


def solver_fingerprint(cfg) -> str:
    """sha256 and mtime of bin/main, plus extend_z3's HEAD and whether its tree is
    dirty. Read-only: --no-optional-locks keeps git from refreshing the index."""
    import hashlib
    b = cfg.path(cfg.data["solver"]["mix"]["bin"])
    if not b.exists():
        return "missing"
    h = hashlib.sha256(b.read_bytes()).hexdigest()[:12]
    mtime = datetime.datetime.fromtimestamp(b.stat().st_mtime).strftime("%Y-%m-%d %H:%M")
    repo = b.parent.parent
    git = ["git", "--no-optional-locks", "-C", str(repo)]
    head = subprocess.run(git + ["rev-parse", "--short", "HEAD"], capture_output=True, text=True).stdout.strip()
    dirty = subprocess.run(git + ["status", "--porcelain", "--untracked-files=no"],
                           capture_output=True, text=True).stdout.strip()
    return f"sha256 {h}…, built {mtime}, extend_z3 HEAD {head or '?'}{' + uncommitted changes' if dirty else ''}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--no-solve", action="store_true", help="skip bin/main in A0.2")
    ap.add_argument("--no-systemd", action="store_true")
    args = ap.parse_args()

    cfg = config.load()
    stamp = datetime.date.today().isoformat()
    logs = ROOT / "work" / "phase0" / stamp
    golden = [str(cfg.golden_root / s) for s in cfg.data["golden"]["sets"]]
    py = [sys.executable, "-m", "c2mix"]
    rows = []   # (item, PASS/FAIL, seconds, detail, artifact)

    # unit tests
    code, dt, out = run([sys.executable, "-m", "unittest", "discover", "-s", "tests/phase0", "-t", "."],
                        logs / "unittest.log")
    m = re.search(r"Ran (\d+) tests", out)
    rows.append(("unit tests", code == 0, dt, f"{m.group(1) if m else '?'} tests", logs / "unittest.log"))

    # A0.1
    code, dt, out = run(py + ["lint", "--profile=consumer", "--z3", "-q",
                              "--baseline", "tests/phase0/lint-baseline.json"] + golden, logs / "a0.1-lint.log")
    nfiles = out.count(" error(s), warnings ")
    rows.append(("A0.1 lint golden (consumer, baseline)", code == 0, dt,
                 f"{nfiles} files; {out.strip().splitlines()[-1]}", logs / "a0.1-lint.log"))

    # A0.2
    rt = ROOT / "work" / "phase0" / "roundtrip"
    cmd = py + ["roundtrip", "-o", str(rt)] + ([] if args.no_solve else ["--solve"]) + \
        (["--no-systemd"] if args.no_systemd else []) + golden
    code, dt, out = run(cmd, logs / "a0.2-roundtrip.log")
    ident = out.count("bytes identical")
    unsat = len(re.findall(r"bin/main unsat .* OK", out))
    solve_times = [float(x) for x in re.findall(r"bin/main unsat \(([0-9.]+)s", out)]
    detail = f"normalized OK {out.count('normalized OK')}/24, byte-identical {ident}/24"
    if not args.no_solve:
        detail += f", bin/main unsat {unsat}/24 (Σ {sum(solve_times):.1f} s)"
    rows.append(("A0.2 round-trip" + (" (no solve)" if args.no_solve else ""), code == 0, dt, detail,
                 logs / "a0.2-roundtrip.log"))

    # A0.3
    neg = sorted((ROOT / "tests/phase0/negative").glob("*.smt2"))
    bad = []
    for f in neg:
        got = {d.code for d in lint.lint_file(f, "strict", cfg if f.stem == "PARSE" else None)}
        if got != {f.stem}:
            bad.append(f"{f.stem}: {sorted(got)}")
    covered = {f.stem for f in neg} == set(lint.RULES)
    rows.append(("A0.3 negative corpus", not bad and covered, 0.0,
                 f"{len(neg)} files / {len(lint.RULES)} rules" + (f"; mismatches {bad}" if bad else "")
                 + ("" if covered else "; rules without a file"), ROOT / "tests/phase0/negative"))

    # G10 (checked from phase 0 on)
    p = subprocess.run(["grep", "-riEn", G10, "c2mix/"], cwd=ROOT, capture_output=True, text=True)
    hits = [ln for ln in p.stdout.splitlines() if "__pycache__" not in ln]
    rows.append(("G10 core has no scheme knowledge", not hits, 0.0,
                 f"{len(hits)} hits" + (f": {hits[:3]}" if hits else ""), ROOT / "c2mix"))

    ok = all(r[1] for r in rows)
    lines = [f"# 第 0 階段驗收 — {stamp}", "",
             f"整體：**{'PASS' if ok else 'FAIL'}**（A0.1–A0.3 與 G10 為關卡；A0.4 見下方）", "",
             f"- bin/main：`{cfg.path(cfg.data['solver']['mix']['bin'])}`（{solver_fingerprint(cfg)}）",
             f"- golden：`{cfg.golden_root}` 下的 {', '.join(cfg.data['golden']['sets'])}", "",
             "| 項目 | 結果 | 耗時 (s) | 細節 | 產物 |", "|---|---|---:|---|---|"]
    for item, passed, dt, detail, art in rows:
        lines.append(f"| {item} | {'PASS' if passed else 'FAIL'} | {dt:.1f} | {detail} | `{Path(art).relative_to(ROOT)}` |")
    lines += ["", "## A0.4", ""]
    a04 = sorted((ROOT / "reports").glob("a0.4-*.md"))
    lines.append(f"最新結果：`{a04[-1].relative_to(ROOT)}`（由 `make ab-0` 產生）" if a04 else
                 "尚未執行（`make ab-0`）。")
    path = ROOT / "reports" / f"accept-0-{stamp}.md"
    path.write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    print(f"\nreport: {path}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
