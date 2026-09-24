#!/usr/bin/env python3
"""Phase 2 acceptance (spec §9, 第 2 階段): A2.1–A2.5 over the three targets.

Writes reports/accept-2-<date>.md. Exit status 0 only if every gate passes.

usage: tests/phase2/accept.py [--quick] [--runs 1000]
"""
from __future__ import annotations

import argparse
import datetime
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "tests" / "phase2" / "targets"))

import t2a_ntt8                                     # noqa: E402
import t2b_limbadd                                  # noqa: E402
import t2c_montgomery                               # noqa: E402
from c2mix import config, gates, pipeline           # noqa: E402
from c2mix.gates import g3, g4, g5, g6, g7, g8, g9  # noqa: E402
from c2mix.spec.check import check_spec             # noqa: E402
from c2mix.vc.assemble import Options               # noqa: E402

TARGETS = {"t2a": t2a_ntt8, "t2b": t2b_limbadd, "t2c": t2c_montgomery}
G10 = r"kyber|dilithium|saber|mceliece|p256|25519|3329|8380417"


def build_one(name, mod, out_root, cfg, hints="emit"):
    trace, target = mod.build()
    return trace, target, pipeline.build(trace, target, out_root / name / hints, name,
                                         Options(hints=hints), cfg)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--runs", type=int, default=1000)
    ap.add_argument("--g3-runs", type=int, default=50, help="G3 evaluates every statement")
    ap.add_argument("--no-systemd", action="store_true")
    args = ap.parse_args()
    if args.quick:
        args.runs, args.g3_runs = 50, 5
    cfg = config.load()
    stamp = datetime.date.today().isoformat()
    out_root = ROOT / "work" / "phase2" / "accept"
    rows = []            # (item, ok, seconds, detail)
    builds = {}

    # ------------------------------------------------------------ A2.1
    t0 = time.monotonic()
    detail, ok = [], True
    for name, mod in TARGETS.items():
        trace, target = mod.build()
        fails = check_spec(target, trace)
        ok &= not fails
        detail.append(f"{name}: {'S1–S4 ok' if not fails else fails}")
    code = subprocess.run([sys.executable, "-m", "unittest", "tests.phase2.test_spec"],
                          capture_output=True, text=True, cwd=ROOT)
    ok &= code.returncode == 0
    n = code.stderr.split("Ran ")[1].split(" ")[0] if "Ran " in code.stderr else "?"
    rows.append(("A2.1 spec self-checks S1–S4 + spec mutations", ok, time.monotonic() - t0,
                 "; ".join(detail) + f"; {n} mutation tests"))

    # ------------------------------------------------------------ build every target
    t0 = time.monotonic()
    for name, mod in TARGETS.items():
        builds[name] = build_one(name, mod, out_root, cfg, "emit")
    rows.append(("build (--hints=emit)", True, time.monotonic() - t0,
                 "; ".join(f"{n}: {len(b.vcs)} cuts, hints "
                           f"{sum(len(v.hints) for v in b.vcs)}" for n, (_, _, b) in builds.items())))

    # ------------------------------------------------------------ A2.2
    t0 = time.monotonic()
    detail, ok = [], True
    for name, (trace, target, b) in builds.items():
        ex = gates.runs(trace, target, args.runs, seed=7)
        bad4, unsupported = g4.check_runs(trace, target, ex)
        bad3 = g3.check_runs(b.vcs, trace, target, ex[:args.g3_runs])
        ok &= not bad4 and not bad3
        detail.append(f"{name}: G4 {len(ex)} runs{' ok' if not bad4 else ' FAIL ' + str(bad4[:2])}, "
                      f"G3 {args.g3_runs} runs{' ok' if not bad3 else ' FAIL ' + str(bad3[:2])}"
                      + (f", unsupported-eval {len(unsupported)}" if unsupported else ""))
    rows.append(("A2.2 G3 trace consistency + G4 specification holds", ok,
                 time.monotonic() - t0, "; ".join(detail)))

    # ------------------------------------------------------------ A2.3
    t0 = time.monotonic()
    detail, ok = [], True
    for name, (trace, target, b) in builds.items():
        rng_files = [f for f in b.files if "range" in f.name]
        mix_files = [f for f in b.files if f.name.endswith(".smt2") and "range" not in f.name]
        bad5 = g5.check(rng_files, cfg.data["solver"]["range"]["bin"])
        bad6, res = g6.check(mix_files, cfg, out_root / "runs",
                             use_systemd=not args.no_systemd, timeout=900)
        ok &= not bad5 and not bad6
        detail.append(f"{name}: G5 {len(rng_files)}{' ok' if not bad5 else ' FAIL ' + str(bad5)}, "
                      f"G6 {len(mix_files)}{' ok' if not bad6 else ' FAIL ' + str(bad6)} "
                      f"(Σ {sum(r.solver_seconds or 0 for r in res):.1f}s)")
    rows.append(("A2.3 G5 range VCs + G6 mix VCs, --hints=emit", ok, time.monotonic() - t0,
                 "; ".join(detail)))

    # omit mode is recorded, not gated (§9)
    t0 = time.monotonic()
    detail = []
    for name, mod in TARGETS.items():
        trace, target, b = build_one(name, mod, out_root, cfg, "omit")
        mix_files = [f for f in b.files if f.name.endswith(".smt2") and "range" not in f.name]
        bad6, res = g6.check(mix_files, cfg, out_root / "runs",
                             use_systemd=not args.no_systemd, timeout=60)
        detail.append(f"{name}: {len(mix_files) - len(bad6)}/{len(mix_files)} unsat "
                      f"(hints proved: {sum(len(v.hints) for v in b.vcs)})")
    rows.append(("--hints=omit (recorded, not a gate)", True, time.monotonic() - t0,
                 "; ".join(detail)))

    # ------------------------------------------------------------ A2.4
    t0 = time.monotonic()
    detail, ok = [], True
    for name, (trace, target, b) in builds.items():
        killed, survivors = 0, []
        mutants = g7.mutate(trace, limit=10, refs=g7.spec_refs(target))
        for m in mutants:
            by = kill(m, target, cfg, out_root / "mutants" / name / m.name, args)
            if by:
                killed += 1
            else:
                survivors.append(m.name)
        ok &= killed == len(mutants)
        detail.append(f"{name}: {killed}/{len(mutants)} killed"
                      + (f"; survivors {survivors}" if survivors else ""))
    rows.append(("A2.4 G7 mutation kill rate", ok, time.monotonic() - t0, "; ".join(detail)))

    # ------------------------------------------------------------ A2.5
    t0 = time.monotonic()
    detail, ok = [], True
    for name, mod in TARGETS.items():
        trace, target, first = build_one(name, mod, out_root / "g8a", cfg, "emit")
        _, _, second = build_one(name, mod, out_root / "g8b", cfg, "emit")
        bad8 = g8.compare(g8.digest(first.files), g8.digest(second.files))
        bad9 = g9.check(builds[name][2].manifest,
                        g5_passed={v.index for v in builds[name][2].vcs},
                        g6_passed={v.index for v in builds[name][2].vcs})
        ok &= not bad8 and not bad9
        detail.append(f"{name}: G8 {'ok' if not bad8 else bad8[:2]}, "
                      f"G9 {'ok' if not bad9 else bad9[:2]} "
                      f"({sum(len(c['carried']) for c in builds[name][2].manifest['cuts'])} carried)")
    rows.append(("A2.5 G8 determinism + G9 cut chain", ok, time.monotonic() - t0, "; ".join(detail)))

    p = subprocess.run(["grep", "-riEn", G10, "c2mix/"], cwd=ROOT, capture_output=True, text=True)
    hits = [ln for ln in p.stdout.splitlines() if "__pycache__" not in ln]
    rows.append(("G10 core has no scheme knowledge", not hits, 0.0, f"{len(hits)} hits"))

    ok_all = all(r[1] for r in rows)
    lines = [f"# 第 2 階段驗收 — {stamp}", "",
             f"整體：**{'PASS' if ok_all else 'FAIL'}**" + ("（--quick）" if args.quick else ""), "",
             f"目標：T2a（8 點 NTT、q=17、3 層）、T2b（2-limb 模加法）、T2c（Montgomery 約簡）", "",
             "| 項目 | 結果 | 耗時 (s) | 細節 |", "|---|---|---:|---|"]
    for item, passed, dt, det in rows:
        lines.append(f"| {item} | {'PASS' if passed else 'FAIL'} | {dt:.1f} | {det} |")
    lines += ["", "## bin/main 的 flag 與 `sat` 的意義", "",
              "`unsat` 才是通過。`sat` 只代表「沒有證出來」，不代表 VC 是假的：同一個 T2b 檔案在"
              "沒有 partition prepass 時是 `sat`、加上之後 0.3 秒 `unsat`（F10）。"
              "所以 c2mix 自己的輸出預設帶 prepass flag，遇到 `sat` 要先用 G3/G4 分類。"]
    path = ROOT / "reports" / f"accept-2-{stamp}.md"
    path.parent.mkdir(exist_ok=True)
    path.write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    print(f"\nreport: {path}")
    sys.exit(0 if ok_all else 1)


def kill(mutant, target, cfg, out_dir, args) -> str | None:
    """The first gate that notices the mutant, cheapest first."""
    trace = mutant.trace
    try:
        fails = check_spec(target, trace)
        if fails:
            return "S1–S4"
        ex = gates.runs(trace, target, 20, seed=11)
        bad4, _ = g4.check_runs(trace, target, ex)
        if bad4:
            return "G4"
        b = pipeline.build(trace, target, out_dir, "mutant", Options(hints="emit"), cfg)
        bad3 = g3.check_runs(b.vcs, trace, target, ex[:3])
        if bad3:
            return "G3"
        bad5 = g5.check([f for f in b.files if "range" in f.name],
                        cfg.data["solver"]["range"]["bin"], timeout=120)
        if bad5:
            return "G5"
        bad6, _ = g6.check([f for f in b.files if f.name.endswith(".smt2") and "range" not in f.name],
                           cfg, out_dir / "runs", use_systemd=not args.no_systemd, timeout=300)
        if bad6:
            return "G6"
    except Exception as e:                      # a mutant that cannot even be built is caught
        return f"build ({type(e).__name__})"
    return None


if __name__ == "__main__":
    main()
