#!/usr/bin/env python3
"""Phase 4 acceptance (spec §9, 第 4 階段): A4.1–A4.6 over the phase 4 targets.

Writes reports/accept-4-<date>.md. Exit status 0 only if every gate passes.

usage: tests/phase4/accept.py [--quick] [--targets a,b] [--skip-omit] [--skip-g7]
"""
from __future__ import annotations

import argparse
import datetime
import resource
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from c2mix import config, gates, pipeline, targets                      # noqa: E402
from c2mix.gates import g1, g2, g3, g4, g5, g6, g7, g8, g9              # noqa: E402
from c2mix.ir.trace import ENTRY_POINT                                  # noqa: E402
from c2mix.vc.assemble import Options, entry_intervals                  # noqa: E402
from tests.phase4 import golden                                         # noqa: E402

G10 = r"kyber|dilithium|saber|mceliece|p256|25519|3329|8380417"
WORK = ROOT / "work" / "phase4"
MUST_PASS = ("kyber_ntt", "fiat_p256_mul")          # A4.3: the goldens are known solvable
VARIANTS = {"kyber_ntt": ["half"]}                   # built and solved beside the default
KYBER_GOLDEN = "pqclean_kyber768_avx2_noAssume"
P256_GOLDEN = "openssl/ecp_nistz256/x86_64"
P256_PAIRS = {                                       # A4.2's table
    "fiat_p256_mul": ["ecp_nistz256_mul_mont_0", "ecp_nistz256_mul_mont_1"],
    "fiat_p256_sub": ["ecp_nistz256_sub_0", "ecp_nistz256_sub_v2_0"],
    "fiat_p256_opp": ["ecp_nistz256_neg_0"],
    "fiat_p256_to_montgomery": ["ecp_nistz256_to_mont_0"],
    "fiat_p256_from_montgomery": ["ecp_nistz256_from_mont_0"],
}
BUDGET_GEN_S, BUDGET_RSS_KIB, BUDGET_RANGE_S = 300, 8 << 20, 600      # A4.6


def peak_rss_kib() -> int:
    """This process or its largest child so far (hint discovery's z3 runs), in KiB."""
    return max(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
               resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)


def build_target(name, cfg, hints="emit", variant=None, mutate=None, work=None):
    """Frontend + VCs. Returns (target, frontend, build, out dir, seconds, executor s)."""
    t = targets.load(name)
    tag = name + (f"-{variant}" if variant else "")
    work = work or WORK / tag
    t0 = time.monotonic()
    fe = targets.prepare(t, work, variant=variant, mutate=mutate)
    t_exec = time.monotonic() - t0
    out = work / ("out" if hints == "emit" else f"out-{hints}")
    build = pipeline.build(fe.trace, fe.spec, out, tag, Options(hints=hints), cfg,
                           range_split=t.range_split, spec_source=str(t.path / "spec.py"),
                           frontend=fe.stats)
    return t, fe, build, out, time.monotonic() - t0, t_exec


def mix_files(build, out) -> list[Path]:
    return [out / f"cut{vc.index}.smt2" for vc in build.vcs]


def range_files(build) -> list[Path]:
    return [f for f in build.files if ".range" in f.name]


def g5_timed(files, z3: str, jobs: int, timeout: float = BUDGET_RANGE_S):
    """G5 over many files in parallel: (failures, slowest file seconds, total seconds)."""
    def one(f):
        t0 = time.monotonic()
        ok, got = g5.check_file(f, z3, timeout)
        return f, ok, got, time.monotonic() - t0
    with ThreadPoolExecutor(max(1, jobs)) as ex:
        res = list(ex.map(one, files))
    bad = [f"{f.name}: {got}" for f, ok, got, _ in res if not ok]
    return bad, max((r[3] for r in res), default=0.0), sum(r[3] for r in res)


def pre_extremes(trace, spec) -> list[dict]:
    """A4.1's extreme patterns, from the precondition's per-value intervals: every
    element at its lower end, every element at its upper end, and the two alternations
    (for Kyber: all ±(q−1), and signs alternating)."""
    bounds = entry_intervals(spec, trace, ENTRY_POINT)
    objs = g2.input_objects(trace)
    out = []
    for pick in (lambda i: 0, lambda i: 1, lambda i: i % 2, lambda i: 1 - i % 2):
        vec, k = {}, 0
        for obj in sorted(objs):
            vals = []
            for idx in sorted(objs[obj]):
                v = next(x for x in trace.prog.inputs if x.name == objs[obj][idx])
                span = bounds.get(v.name)
                lo, hi = (span.lo, span.hi) if span else (v.lo, v.hi)
                vals.append((lo, hi)[pick(k)])
                k += 1
            vec[obj] = vals
        out.append(vec)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--targets", help="comma separated subset")
    ap.add_argument("--g2-runs", type=int, default=10000)
    ap.add_argument("--runs", type=int, default=1000, help="G4 runs")
    ap.add_argument("--g3-runs", type=int, default=20)
    ap.add_argument("--mutants", type=int, default=20)
    ap.add_argument("--jobs", type=int, default=6, help="parallel z3 for G5")
    ap.add_argument("--g6-timeout", type=float, default=1800)
    ap.add_argument("--omit-timeout", type=float, default=600,
                    help="bin/main timeout per file for the --hints=omit record")
    ap.add_argument("--no-systemd", action="store_true")
    ap.add_argument("--skip-omit", action="store_true")
    ap.add_argument("--skip-g7", action="store_true")
    ap.add_argument("--skip-variants", action="store_true")
    args = ap.parse_args()
    if args.quick:
        args.g2_runs, args.runs, args.g3_runs, args.mutants = 500, 50, 3, 4
    cfg = config.load()
    z3 = cfg.data["solver"]["range"]["bin"]
    names = args.targets.split(",") if args.targets else targets.names(phase=4)
    stamp = datetime.date.today().isoformat()
    rows, notes, perf = [], [], []
    built = {}

    def row(item, ok, seconds, detail):
        rows.append((item, ok, seconds, detail))
        print(f"[{'PASS' if ok else 'FAIL'}] {item} ({seconds:.1f}s) {detail}", flush=True)
        return ok

    # ---------------------------------------------------------------- build
    t0 = time.monotonic()
    detail, ok = [], True
    for name in names:
        for variant in [None] + ([] if args.skip_variants else VARIANTS.get(name, [])):
            tag = name + (f"-{variant}" if variant else "")
            try:
                t, fe, build, out, secs, t_exec = build_target(name, cfg, variant=variant)
                built[tag] = (t, fe, build, out)
                n_hints = sum(len(v.hints) for v in build.vcs)
                detail.append(f"{tag}: {len(build.vcs)} VC(s), {len(range_files(build))} range "
                              f"file(s), {fe.stats['instructions']} instrs, {n_hints} hints, "
                              f"{secs:.0f}s")
                perf.append([tag, secs, t_exec, fe.stats["steps"], peak_rss_kib(), None])
            except Exception as e:
                ok = False
                detail.append(f"{tag}: {type(e).__name__}: {str(e)[:120]}")
    row("build (--hints=emit)", ok, time.monotonic() - t0, "; ".join(detail))

    # ---------------------------------------------------------------- A4.1
    t0 = time.monotonic()
    ok, detail = True, []
    for tag, (t, fe, build, out) in built.items():
        binary = targets.native(t, fe)
        vecs, exhaustive = g2.vectors(fe.trace, args.g2_runs)
        vecs += pre_extremes(fe.trace, fe.spec)
        rep = g2.check(fe.trace, binary, vecs, fe.work / "g2")
        ok &= rep.ok
        detail.append(f"{tag}: {len(vecs)}{'!' if exhaustive else ''} vectors, "
                      f"{len(fe.trace.snapshots) - 1} snapshot(s) each, {rep.compared} compared"
                      + ("" if rep.ok else f" FAIL {rep.mismatches[:1]}"))
    row("A4.1 G2 with every cut's snapshot (random + extremes; ! = exhaustive)", ok,
        time.monotonic() - t0, "; ".join(detail))

    # ---------------------------------------------------------------- A4.2
    t0 = time.monotonic()
    ok, detail = True, []
    if "kyber_ntt" in built:
        t, fe, build, out = built["kyber_ntt"]
        params = __import__("targets.kyber_ntt.params", fromlist=["Q"])
        good, msg = golden.kyber(cfg.golden_root / KYBER_GOLDEN, mix_files(build, out),
                                 fe.spec, params.Q)
        ok &= good
        detail.append(f"kyber_ntt: {msg}")
    for name, golds in P256_PAIRS.items():
        if name not in built:
            continue
        t, fe, build, out = built[name]
        p = __import__(f"targets.{name}.params", fromlist=["P"]).P
        roles = golden.roles(fe.trace)
        for g in golds:
            path = cfg.golden_root / P256_GOLDEN / f"{g}.smt2"
            good, msg = golden.p256_post(path, out / "cut0.smt2", p, roles)
            ok &= good
            parts = [f"{name} vs {g}: {msg}"]
            if not g.endswith("_1"):
                good, msg = golden.p256_pre(path, out / "cut0.smt2", p, roles)
                ok &= good
                parts.append(msg)
            detail.append("; ".join(parts))
    row("A4.2 mathematical layer vs the goldens", ok, time.monotonic() - t0,
        " | ".join(detail) or "no target with a golden in this subset")

    # ---------------------------------------------------------------- A4.3
    t0 = time.monotonic()
    ok, detail = True, []
    for tag, (t, fe, build, out) in built.items():
        bad5, slowest, total5 = g5_timed(range_files(build), z3, args.jobs)
        bad6, res = g6.check(mix_files(build, out), cfg, out / "_runs",
                             use_systemd=not args.no_systemd, timeout=args.g6_timeout)
        secs = sum(r.solver_seconds or r.wall_seconds for r in res)
        rss = max((r.maxrss_kib or 0 for r in res), default=0)
        good = not (bad5 or bad6)
        if bad6 and not t.must_pass:
            notes.append(f"{tag}: G6 not unsat on {len(bad6)} VC(s) ({bad6[0]}); must_pass = "
                         "false, so this is recorded for R6 classification, not a gate")
            good = not bad5
        ok &= good
        for p in perf:
            if p[0] == tag:
                p[5] = slowest
        detail.append(f"{tag}: G5 {'ok' if not bad5 else bad5[:2]} (slowest file "
                      f"{slowest:.0f}s, Σ {total5:.0f}s), G6 "
                      f"{len(res) - len(bad6)}/{len(res)} unsat (Σ {secs:.1f}s, MaxRSS "
                      f"{rss / 1048576:.2f} GiB)")
    row("A4.3 G5 + G6, --hints=emit (must pass: " + ", ".join(MUST_PASS) + ")", ok,
        time.monotonic() - t0, "; ".join(detail))

    if not args.skip_omit:
        t0 = time.monotonic()
        ok, detail = True, []
        for tag in list(built):
            name = tag.split("-")[0]
            variant = tag.split("-")[1] if "-" in tag else None
            try:
                t, fe2, build2, out2, _, _ = build_target(name, cfg, hints="omit",
                                                          variant=variant)
                bad6, res = g6.check(mix_files(build2, out2), cfg, out2 / "_runs",
                                     use_systemd=not args.no_systemd,
                                     timeout=args.omit_timeout)
                secs = sum(r.solver_seconds or r.wall_seconds for r in res)
                rss = max((r.maxrss_kib or 0 for r in res), default=0)
                # target.toml [expect] hints_omit: "record" (the default) makes this a
                # record, as for the golden's own noAssume set; "gate" makes it a gate
                gate = t.data.get("expect", {}).get("hints_omit", "record") == "gate"
                ok &= not (gate and bad6)
                detail.append(f"{tag}: {len(res) - len(bad6)}/{len(res)} unsat (Σ {secs:.1f}s, "
                              f"MaxRSS {rss / 1048576:.2f} GiB)" + (" [gate]" if gate else ""))
            except Exception as e:
                ok = False
                detail.append(f"{tag}: {type(e).__name__}: {str(e)[:80]}")
        row("A4.3 G6, --hints=omit (a gate only where target.toml says hints_omit = gate)", ok,
            time.monotonic() - t0, "; ".join(detail))

    # ---------------------------------------------------------------- A4.5
    t0 = time.monotonic()
    ok, detail = True, []
    for tag, (t, fe, build, out) in built.items():
        errs, warns = g1.check(mix_files(build, out) + range_files(build), "consumer", cfg)
        runs = gates.runs(fe.trace, fe.spec, args.g3_runs)
        bad3 = g3.check_runs(build.vcs, fe.trace, fe.spec, runs)
        more = gates.runs(fe.trace, fe.spec, args.runs, seed=1)
        bad4, unsupported = g4.check_runs(fe.trace, fe.spec, more)
        again = pipeline.build(fe.trace, fe.spec, fe.work / "out-again", tag,
                               Options(hints="emit"), cfg, range_split=t.range_split,
                               spec_source=str(t.path / "spec.py"), frontend=fe.stats)
        bad8 = g8.compare(g8.digest(build.files), g8.digest(again.files))
        bad9 = g9.check(build.manifest)
        good = not (errs or bad3 or bad4 or bad8 or bad9)
        ok &= good
        detail.append(f"{tag}: G1 {len(errs)} err {warns or '{}'}, G3 {args.g3_runs} runs "
                      f"{'ok' if not bad3 else bad3[:1]}, G4 {args.runs} runs "
                      f"{'ok' if not bad4 else bad4[:1]}, G8 {'ok' if not bad8 else bad8[:1]}, "
                      f"G9 {'ok' if not bad9 else bad9[:1]}"
                      + (f", unsupported-eval {unsupported}" if unsupported else ""))
    row("A4.5 G1 + G3 + G4 + G8 + G9", ok, time.monotonic() - t0, "; ".join(detail))

    # ---------------------------------------------------------------- A4.4
    if not args.skip_g7:
        t0 = time.monotonic()
        ok, detail = True, []
        for name in names:
            killed, survived, total, equivalent = mutation_run(name, cfg, z3, args)
            enough = total - equivalent >= min(20, args.mutants)
            ok &= not survived and enough
            detail.append(f"{name}: {killed}/{total - equivalent} killed"
                          + (f", {equivalent} equivalent" if equivalent else "")
                          + (f", SURVIVED {survived}" if survived else "")
                          + ("" if enough else ", fewer than 20 non-equivalent mutants"))
        row(f"A4.4 G7, {args.mutants} C mutants per target", ok, time.monotonic() - t0,
            "; ".join(detail))

    # ---------------------------------------------------------------- A4.6
    ok, detail = True, []
    for tag, secs, t_exec, steps, rss, slowest in perf:
        good = secs <= BUDGET_GEN_S and rss <= BUDGET_RSS_KIB and \
            (slowest is None or slowest <= BUDGET_RANGE_S)
        ok &= good
        detail.append(f"{tag}: generation {secs:.0f}s (executor {t_exec:.1f}s, {steps} steps), "
                      f"peak RSS so far {rss / 1048576:.2f} GiB, slowest range file "
                      + ("—" if slowest is None else f"{slowest:.0f}s"))
    row(f"A4.6 budgets (≤ {BUDGET_GEN_S}s, ≤ 8 GiB, range file ≤ {BUDGET_RANGE_S}s)", ok, 0.0,
        "; ".join(detail))

    # ---------------------------------------------------------------- G10
    t0 = time.monotonic()
    p = subprocess.run(["grep", "-riEn", G10, str(ROOT / "c2mix"), str(ROOT / "include"),
                        str(ROOT / "runtime"), "--exclude-dir=__pycache__"],
                       capture_output=True, text=True)
    hits = [l for l in p.stdout.splitlines() if l.strip()]
    row("G10 core has no scheme knowledge", not hits, time.monotonic() - t0,
        f"{len(hits)} hit(s)" + (f": {hits[:3]}" if hits else ""))

    report(rows, notes, stamp, list(built))
    return 0 if all(r[1] for r in rows) else 1


# --------------------------------------------------------------------- A4.4
def mutation_run(name: str, cfg, z3: str, args) -> tuple[int, list, int, int]:
    """C-source mutants (G7): as in phase 3, a mutant that changes nothing this target
    executes, or that computes the same thing on every precondition-satisfying input,
    is counted as equivalent rather than killed."""
    from tests.phase3.accept import _same_behaviour, _vector
    t = targets.load(name)
    base_fe = targets.prepare(t, WORK / name / "mutbase")
    executed = {o["function"] for o in base_fe.trace.origins.values() if "function" in o}
    mutants = []
    per_file = max(1, -(-args.mutants // max(1, len(t.files))))
    for source in t.files:
        text = (t.vendor / source).read_text()
        lines = g7.function_lines(text, executed) or None
        if lines is None:
            continue
        mutants += g7.mutate_source(text, source, per_file * 2, lines)
    mutants = mutants[:max(args.mutants, 20)]
    baseline = str(base_fe.trace.prog)
    base_runs = gates.runs(base_fe.trace, base_fe.spec, 40, seed=7)
    vectors = [_vector(base_fe.trace, values) for values, _ in base_runs]
    base_out = [g2.trace_snapshots(base_fe.trace, v) for v in vectors]

    killed, survived, equivalent = 0, [], 0
    for m in mutants:
        work = WORK / "mutants" / name / m.name.replace("/", "_")
        try:
            _, fe, build, out, _, _ = build_target(name, cfg, mutate={m.path: m.text},
                                                   work=work)
        except Exception:
            killed += 1                      # the frontend or the spec check refused it
            continue
        if str(fe.trace.prog) == baseline:
            equivalent += 1
            continue
        try:
            runs = gates.runs(fe.trace, fe.spec, 40, seed=7)
        except RuntimeError:
            killed += 1
            continue
        if g4.check_runs(fe.trace, fe.spec, runs)[0]:
            killed += 1
            continue
        if g5_timed(range_files(build), z3, args.jobs)[0]:
            killed += 1
            continue
        bad6, _ = g6.check(mix_files(build, out), cfg, out / "_runs", timeout=300)
        if bad6:
            killed += 1
        elif _same_behaviour(fe.trace, vectors, base_out):
            equivalent += 1
        else:
            survived.append(f"{m.name} ({m.description})")
    return killed, survived, len(mutants), equivalent


# -------------------------------------------------------------------- report
def report(rows, notes, stamp, names) -> None:
    out = ROOT / "reports" / f"accept-4-{stamp}.md"
    out.parent.mkdir(parents=True, exist_ok=True)
    overall = "PASS" if all(r[1] for r in rows) else "FAIL"
    lines = [f"# 第 4 階段驗收 — {stamp}", "", f"整體：**{overall}**", "",
             f"目標（{len(names)}）：" + "、".join(names), "",
             "| 項目 | 結果 | 耗時 (s) | 細節 |", "|---|---|---:|---|"]
    for item, ok, secs, detail in rows:
        lines.append(f"| {item} | {'PASS' if ok else 'FAIL'} | {secs:.1f} | {detail} |")
    if notes:
        lines += ["", "## 備註", ""] + [f"- {n}" for n in notes]
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"\nwrote {out}")


if __name__ == "__main__":
    sys.exit(main())
