#!/usr/bin/env python3
"""Phase 1 acceptance (spec §9, 第 1 階段): A1.1–A1.5 plus G10.

Writes reports/accept-1-<date>.md. Exit status 0 only if every gate passes.

usage: tests/phase1/accept.py [--quick] [--jobs 12]
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
sys.path.insert(0, str(ROOT / "tests" / "phase1"))

import fuzz                                    # noqa: E402
import property as prop                        # noqa: E402
from c2mix import config                       # noqa: E402
from c2mix.lower import lemmas                 # noqa: E402

G10 = r"kyber|dilithium|saber|mceliece|p256|25519|3329|8380417"
# z3 cannot do these in reasonable time; property tests cover them instead (A1.1).
NO_SOLVER = {("L4", 64), ("L4'", 64), ("L4", 128), ("L4'", 128)}


def width_of(name: str) -> int:
    return int(name.split(".w")[1].split(".")[0])


def keep(L) -> bool:
    return (L.rule, width_of(L.name)) not in NO_SOLVER


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true", help="smaller fuzz and property runs")
    ap.add_argument("--jobs", type=int, default=12)
    ap.add_argument("--timeout", type=float, default=120)
    args = ap.parse_args()
    cfg = config.load()
    z3 = cfg.data["solver"]["range"]["bin"]
    stamp = datetime.date.today().isoformat()
    rows = []            # (item, ok, seconds, detail)

    # ---------------------------------------------------------------- A1.1 / A1.2
    base_mixed = [L for L in lemmas.generate(widths=(4,)) if "128" not in L.name]
    wide = tuple(w for w in (4, 8, 16, 32, 64) if not args.quick or w <= 16)
    base_bv = [L for L in lemmas.generate(widths=wide) if keep(L)]

    t0 = time.monotonic()
    res = lemmas.check_all(base_mixed, z3, args.jobs, args.timeout)
    bad = [(L.name, L.expect, got) for L, ok, got in res if not ok]
    rows.append(("A1.1 rule lemmas, emitted encoding (w=4)", not bad, time.monotonic() - t0,
                 f"{len(base_mixed)} lemmas over {len({L.rule for L in base_mixed})} rules"
                 + (f"; failures {bad[:3]}" if bad else "")))

    t0 = time.monotonic()
    items = [lemmas.render_bv(L) for L in base_bv]
    res = lemmas.check_all(items, z3, args.jobs, args.timeout)
    bad = [(L.name, L.expect, got) for L, ok, got in res if not ok]
    rows.append(("A1.1 rule lemmas, QF_BV image (w=" + ",".join(map(str, wide)) + ")",
                 not bad, time.monotonic() - t0,
                 f"{len(items)} lemmas" + (f"; failures {bad[:3]}" if bad else "")))

    t0 = time.monotonic()
    muts = [lemmas.render_bv(m) for L in base_bv for m in lemmas.mutate(L)]
    muts += [m for L in base_mixed for m in lemmas.mutate(L)]
    res = lemmas.check_all(muts, z3, args.jobs, args.timeout)
    bad = [(L.name, L.expect, got) for L, ok, got in res if not ok]
    eq = [L.name for L, ok, _ in res if L.equivalent]
    per_rule = {}
    for L, ok, got in res:
        if ok and not L.equivalent:
            per_rule.setdefault(L.rule, set()).add(L.mutation)
    thin = {r: sorted(k) for r, k in per_rule.items() if len(k) < 3}
    rows.append(("A1.2 lemma mutations", not bad and not thin, time.monotonic() - t0,
                 f"{len(muts)} mutants, {len(muts) - len(bad) - len(eq)} killed, "
                 f"{len(eq)} equivalent (certified)"
                 + (f"; failures {bad[:3]}" if bad else "")
                 + (f"; rules with <3 killing mutations {thin}" if thin else "")))

    # ---------------------------------------------------------------- A1.3 / A1.4
    t0 = time.monotonic()
    n_prog, n_in = (50, 20) if args.quick else (1000, 100)
    code = subprocess.run([sys.executable, str(ROOT / "tests/phase1/fuzz.py"),
                           "--programs", str(n_prog), "--inputs", str(n_in)],
                          capture_output=True, text=True, cwd=ROOT)
    ok = code.returncode == 0
    rows.append(("A1.3 statements true on random runs / A1.4 interval containment", ok,
                 time.monotonic() - t0,
                 f"{n_prog} programs x {n_in} inputs; " + code.stdout.strip().splitlines()[-1][:90]))

    # ---------------------------------------------------------------- property tests
    t0 = time.monotonic()
    samples = 20_000 if args.quick else 1_000_000
    details, ok = [], True
    for width in (64, 128):
        for signed in (True, False):
            n, bad_p = prop.check_mul(width, signed, samples)
            ok &= not bad_p
            details.append(f"w{width}{'s' if signed else 'u'}:{n}")
    rows.append(("A1.1 (continued) 64/128-bit multiply by property test", ok,
                 time.monotonic() - t0, f"{samples} samples each: " + " ".join(details)))

    # ---------------------------------------------------------------- A1.5 and units
    t0 = time.monotonic()
    code = subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", "tests/phase1", "-t", "."],
                          capture_output=True, text=True, cwd=ROOT)
    out = code.stdout + code.stderr
    n_tests = out.split("Ran ")[1].split(" ")[0] if "Ran " in out else "?"
    rows.append(("A1.5 golden shapes + phase-1 unit tests", code.returncode == 0,
                 time.monotonic() - t0, f"{n_tests} tests"))

    p = subprocess.run(["grep", "-riEn", G10, "c2mix/"], cwd=ROOT, capture_output=True, text=True)
    hits = [ln for ln in p.stdout.splitlines() if "__pycache__" not in ln]
    rows.append(("G10 core has no scheme knowledge", not hits, 0.0, f"{len(hits)} hits"))

    ok_all = all(r[1] for r in rows)
    lines = [f"# 第 1 階段驗收 — {stamp}", "",
             f"整體：**{'PASS' if ok_all else 'FAIL'}**" + ("（--quick）" if args.quick else ""), "",
             "| 項目 | 結果 | 耗時 (s) | 細節 |", "|---|---|---:|---|"]
    for item, passed, dt, detail in rows:
        lines.append(f"| {item} | {'PASS' if passed else 'FAIL'} | {dt:.1f} | {detail} |")
    lines += ["", "## A1.1 的求解器限制", "",
              "`(規則, 寬度)` 用 z3 證不完、改用性質測試的組合："
              + ", ".join(f"`{r} w{w}`" for r, w in sorted(NO_SOLVER, key=lambda x: (x[1], x[0]))) + "。",
              "", "兩種引理形式：`mixed` 是 c2mix 實際輸出的編碼（bv2nat 與 Int alias），"
              "z3 只有在 w=4 才算得完；`bv` 是同一條引理在 QF_BV 的像，寬度夠大時兩者等價，"
              "由它涵蓋較寬的寬度。細節見 `docs/lemmas.md`。"]
    path = ROOT / "reports" / f"accept-1-{stamp}.md"
    path.parent.mkdir(exist_ok=True)
    path.write_text("\n".join(lines) + "\n")
    print("\n".join(lines))
    print(f"\nreport: {path}")
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()
