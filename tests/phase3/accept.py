#!/usr/bin/env python3
"""Phase 3 acceptance (spec §9, 第 3 階段): A3.0–A3.9 over the phase 3 targets.

Writes reports/accept-3-<date>.md. Exit status 0 only if every gate passes.

usage: tests/phase3/accept.py [--quick] [--targets a,b] [--g2-runs N]
"""
from __future__ import annotations

import argparse
import datetime
import json
import random
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from c2mix import config, gates, pipeline, targets                      # noqa: E402
from c2mix.frontend import execute, llparse                             # noqa: E402
from c2mix.frontend.toolchain import CFLAGS, Toolchain                  # noqa: E402
from c2mix.gates import g1, g2, g3, g4, g5, g6, g7, g8, g9              # noqa: E402
from c2mix.vc.assemble import Options                                   # noqa: E402
from tests.phase3 import facts                                          # noqa: E402

G10 = r"kyber|dilithium|saber|mceliece|p256|25519|3329|8380417"
WORK = ROOT / "work" / "phase3"
REJECT = ROOT / "tests" / "phase3" / "reject"
ROBUST = ROOT / "tests" / "phase3" / "robust"
CV_REFERENCE = ROOT.parent / "extend_z3" / "working" / "cbmc_small"

# A3.5 pairs a target with the `cv` output of the same program (report only, §9 A3.5).
CV_PAIRS = {"cbmc01_add_comm": "01_add_comm", "cbmc02_montgomery": "02_montgomery",
            "cbmc03_barrett": "03_barrett", "cbmc04_loop_mul": "04_loop_mul"}


def build_target(name, cfg, hints="emit", mutate=None, work=None):
    t = targets.load(name)
    work = work or WORK / name
    fe = targets.prepare(t, work, mutate=mutate)
    out = work / ("out" if hints == "emit" else f"out-{hints}")
    build = pipeline.build(fe.trace, fe.spec, out, name, Options(hints=hints), cfg,
                           spec_source=str(t.path / "spec.py"), frontend=fe.stats)
    return t, fe, build, out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--targets", help="comma separated subset")
    ap.add_argument("--g2-runs", type=int, default=100000)
    ap.add_argument("--runs", type=int, default=1000)
    ap.add_argument("--g3-runs", type=int, default=50)
    ap.add_argument("--mutants", type=int, default=20)
    ap.add_argument("--no-systemd", action="store_true")
    ap.add_argument("--skip-omit", action="store_true", help="skip the --hints=omit record")
    ap.add_argument("--omit-timeout", type=float, default=120,
                    help="bin/main timeout for the --hints=omit record (not a gate)")
    args = ap.parse_args()
    if args.quick:
        args.g2_runs, args.runs, args.g3_runs, args.mutants = 2000, 50, 5, 4
    cfg = config.load()
    z3 = cfg.data["solver"]["range"]["bin"]
    names = args.targets.split(",") if args.targets else targets.names()
    stamp = datetime.date.today().isoformat()
    rows, notes = [], []
    built, ll_paths = {}, {}

    def row(item, ok, seconds, detail):
        rows.append((item, ok, seconds, detail))
        print(f"[{'PASS' if ok else 'FAIL'}] {item} ({seconds:.1f}s) {detail}", flush=True)
        return ok

    # ---------------------------------------------------------------- build
    t0 = time.monotonic()
    detail, ok = [], True
    for name in names:
        try:
            t, fe, build, out = build_target(name, cfg)
            built[name] = (t, fe, build, out)
            ll_paths[name] = fe.ll
            detail.append(f"{name}: {len(build.vcs)} cut(s), {fe.stats['instructions']} instrs, "
                          f"{fe.stats['merges']} merge(s)")
        except Exception as e:
            ok = False
            detail.append(f"{name}: {type(e).__name__}: {e}")
    row("build (--hints=emit)", ok, time.monotonic() - t0, "; ".join(detail))

    # ---------------------------------------------------------------- A3.0
    t0 = time.monotonic()
    results = facts.check_all(WORK / "_facts", ll_paths)
    census = facts.opcode_census(ll_paths)
    ok = all(r[1] for r in results)
    unsupported = [op for op in census if op not in _subset()]
    ok &= not unsupported
    row("A3.0 toolchain facts LF1–LF4 + instruction census", ok, time.monotonic() - t0,
        "; ".join(f"{n}: {d}" for n, _, d in results)
        + f"; opcodes {census}"
        + (f"; OUTSIDE §5.4: {unsupported}" if unsupported else "; all inside §5.4"))

    # ---------------------------------------------------------------- A3.2
    t0 = time.monotonic()
    ok, detail = True, []
    tc = Toolchain()
    for name, ll in ll_paths.items():
        good, msg = roundtrip(tc, Path(ll), WORK / name / "a32")
        ok &= good
        detail.append(f"{name}: {msg}")
    lines_ok, lines_msg = line_numbers(ll_paths, 100)
    ok &= lines_ok
    row("A3.2 parser round-trip (llvm-as, llvm-diff) + line numbers", ok,
        time.monotonic() - t0, "; ".join(detail) + f"; {lines_msg}")

    # ---------------------------------------------------------------- A3.1
    t0 = time.monotonic()
    ok, detail, merge_stats = True, [], {}
    for name, (t, fe, build, out) in built.items():
        binary = targets.native(t, fe)
        vecs, exhaustive = g2.vectors(fe.trace, args.g2_runs)
        rep = g2.check(fe.trace, binary, vecs, fe.work / "g2")
        ok &= rep.ok
        merge_stats[name] = (fe.stats["merges"], fe.stats["merge_depth"])
        detail.append(f"{name}: {len(vecs)}{'!' if exhaustive else ''} vectors, "
                      f"{rep.compared} compared" + ("" if rep.ok else f" FAIL {rep.mismatches[:1]}"))
    row("A3.1 G2 frontend fidelity (! = exhaustive)", ok, time.monotonic() - t0,
        "; ".join(detail))

    # ---------------------------------------------------------------- A3.3
    t0 = time.monotonic()
    ok, detail = True, []
    for name, (t, fe, build, out) in built.items():
        mix = [out / f"cut{vc.index}.smt2" for vc in build.vcs]
        rng = sorted(out.glob("*.range.smt2"))
        errs, warns = g1.check(mix + rng, "consumer", cfg)
        runs = gates.runs(fe.trace, fe.spec, args.g3_runs)
        bad3 = g3.check_runs(build.vcs, fe.trace, fe.spec, runs)
        more = gates.runs(fe.trace, fe.spec, args.runs, seed=1)
        bad4, unsupported = g4.check_runs(fe.trace, fe.spec, more)
        again = pipeline.build(fe.trace, fe.spec, fe.work / "out-again", name,
                               Options(hints="emit"), cfg,
                               spec_source=str(t.path / "spec.py"), frontend=fe.stats)
        bad8 = g8.compare(g8.digest(build.files), g8.digest(again.files))
        good = not (errs or bad3 or bad4 or bad8)
        ok &= good
        detail.append(f"{name}: G1 {len(errs)} err {warns or '{}'}, G3 {args.g3_runs} runs "
                      f"{'ok' if not bad3 else bad3[:1]}, G4 {args.runs} runs "
                      f"{'ok' if not bad4 else bad4[:1]}, G8 {'ok' if not bad8 else bad8[:1]}"
                      + (f", unsupported-eval {unsupported}" if unsupported else ""))
    row("A3.3 G1 + G3 + G4 + G8", ok, time.monotonic() - t0, "; ".join(detail))

    # ---------------------------------------------------------------- A3.4
    t0 = time.monotonic()
    ok, detail = True, []
    for name, (t, fe, build, out) in built.items():
        mix = [out / f"cut{vc.index}.smt2" for vc in build.vcs]
        rng = sorted(out.glob("*.range.smt2"))
        bad5 = g5.check(rng, z3)
        bad6, res = g6.check(mix, cfg, out / "_runs", use_systemd=not args.no_systemd)
        good = not (bad5 or bad6)
        if bad6 and not t.must_pass:
            notes.append(f"{name}: G6 {bad6} — classified under R6, must_pass = false")
            good = not bad5
        ok &= good
        secs = sum(r.solver_seconds or 0 for r in res)
        detail.append(f"{name}: G5 {'ok' if not bad5 else bad5[:1]}, "
                      f"G6 {'ok' if not bad6 else bad6[:1]} (Σ {secs:.1f}s), "
                      f"hints {len([h for v in build.vcs for h in v.hints])}")
    row("A3.4 G5 + G6, --hints=emit", ok, time.monotonic() - t0, "; ".join(detail))

    if not args.skip_omit:
        t0 = time.monotonic()
        detail = []
        for name in names:
            try:
                _, fe2, build2, out2 = build_target(name, cfg, hints="omit",
                                                    work=WORK / name)
                mix = [out2 / f"cut{vc.index}.smt2" for vc in build2.vcs]
                bad6, _ = g6.check(mix, cfg, out2 / "_runs", use_systemd=not args.no_systemd,
                                   timeout=args.omit_timeout)
                detail.append(f"{name}: {len(mix) - len(bad6)}/{len(mix)} unsat "
                              f"(hints proved {len([h for v in build2.vcs for h in v.hints])})")
            except Exception as e:
                detail.append(f"{name}: {type(e).__name__}")
        row(f"--hints=omit (recorded, not a gate; {args.omit_timeout:.0f}s timeout)",
            True, time.monotonic() - t0, "; ".join(detail))

    # ---------------------------------------------------------------- A3.6
    t0 = time.monotonic()
    ok, detail = True, []
    for name in names:
        killed, survived, total, equivalent = mutation_run(name, cfg, z3, args.mutants)
        ok &= not survived
        detail.append(f"{name}: {killed}/{total - equivalent} killed"
                      + (f", {equivalent} equivalent" if equivalent else "")
                      + (f", SURVIVED {survived}" if survived else ""))
    row("A3.6 G7 C-source mutants (equivalent = dead code, or hidden by the "
        "pre-condition)", ok, time.monotonic() - t0, "; ".join(detail))

    # ---------------------------------------------------------------- A3.7
    t0 = time.monotonic()
    ok, detail = True, []
    for src in sorted(REJECT.glob("*.c")):
        want = re.search(r"expect:\s*(\S+)", src.read_text()).group(1)
        got, where, outputs = reject_run(src, WORK / "reject" / src.stem)
        good = got == want and outputs == 0
        ok &= good
        detail.append(f"{src.name}: {got}{'' if good else f' (wanted {want})'}"
                      f"{' @' + where if where else ''}"
                      + (f", {outputs} file(s) written" if outputs else ""))
    row("A3.7 rejection corpus", ok, time.monotonic() - t0, "; ".join(detail))

    # ---------------------------------------------------------------- A3.8
    t0 = time.monotonic()
    ok, detail, codes = True, [], {}
    for src in sorted(ROBUST.glob("*.c")):
        got, where, _ = reject_run(src, WORK / "robust" / src.stem)
        good = got == "ok" or bool(got.startswith("E-") and where)
        ok &= good
        codes[got] = codes.get(got, 0) + 1
        detail.append(f"{src.stem}: {got}")
    row("A3.8 frontend robustness (20 unrelated programs)", ok, time.monotonic() - t0,
        f"{codes}; " + "; ".join(detail))

    # ---------------------------------------------------------------- A3.9
    t0 = time.monotonic()
    merged = {n: s for n, s in merge_stats.items() if s[0]}
    # Over the whole set at least one target has to merge; over a hand-picked subset
    # it is fair for none to.
    ok = bool(merged) or bool(args.targets)
    detail = []
    for name, (n_merges, depth) in merged.items():
        man = json.loads((built[name][3] / "manifest.json").read_text())
        recorded = man.get("frontend", {}).get("merges")
        good = recorded == n_merges
        ok &= good
        detail.append(f"{name}: {n_merges} merge(s), depth {depth}, manifest says {recorded}")
    row("A3.9 input-dependent branches merge; manifest statistics", ok,
        time.monotonic() - t0,
        "; ".join(detail) or "no target in this subset exercises a merge")

    # ---------------------------------------------------------------- A3.5
    t0 = time.monotonic()
    detail = cv_comparison(built, cfg, WORK / "a35", not args.no_systemd)
    row("A3.5 reference comparison with cv mix_0 (report only)", True,
        time.monotonic() - t0, detail)

    # ---------------------------------------------------------------- G10
    t0 = time.monotonic()
    p = subprocess.run(["grep", "-riEn", G10, str(ROOT / "c2mix"), str(ROOT / "include"),
                        str(ROOT / "runtime"), "--exclude-dir=__pycache__"],
                       capture_output=True, text=True)
    hits = [l for l in p.stdout.splitlines() if l.strip()]
    row("G10 core has no scheme knowledge", not hits, time.monotonic() - t0,
        f"{len(hits)} hit(s)" + (f": {hits[:3]}" if hits else ""))

    report(rows, notes, stamp, names)
    return 0 if all(r[1] for r in rows) else 1


def _subset() -> set:
    return (llparse.BINOPS | llparse.CASTS | llparse.TERMINATORS |
            {"icmp", "select", "alloca", "load", "store", "getelementptr", "phi", "call"})


# --------------------------------------------------------------------- A3.2
def roundtrip(tc: Toolchain, ll: Path, work: Path) -> tuple[bool, str]:
    """Strip the debug metadata, parse, print, and let llvm-as and llvm-diff judge."""
    work.mkdir(parents=True, exist_ok=True)
    stripped = tc.strip_debug(ll, work / "stripped.ll")
    mod = llparse.parse(stripped.read_text(), str(stripped))
    printed = work / "printed.ll"
    printed.write_text(llparse.render(mod))
    asm = tc.assemble(printed, work / "printed.bc")
    if asm.returncode != 0:
        return False, f"llvm-as rejected it: {asm.stderr.strip().splitlines()[0][:80]}"
    diff = tc.diff(stripped, printed)
    out = (diff.stdout + diff.stderr).strip()
    return not out, "identical" if not out else f"llvm-diff: {out.splitlines()[0][:80]}"


DBG = re.compile(r"!dbg\s+(![-a-zA-Z$._0-9]+)")
LOC = re.compile(r"^(![-a-zA-Z$._0-9]+)\s*=\s*!DILocation\(line:\s*(\d+)")


def line_numbers(ll_paths: dict, sample: int) -> tuple[bool, str]:
    """A3.2: the line the parser recorded must be the one the !dbg DILocation gives.
    The expected value is read here with its own regex over the raw text."""
    rng = random.Random(3)
    pool = []
    for name, ll in ll_paths.items():
        text = Path(ll).read_text()
        locs = {}
        for line in text.splitlines():
            m = LOC.match(line.strip())
            if m:
                locs[m.group(1)] = int(m.group(2))
        mod = llparse.parse(text, str(ll))
        llparse.attach_lines(mod)
        for f in mod.functions:
            for b in f.blocks:
                for i in b.instrs:
                    m = DBG.search(i.meta or "")
                    if m and m.group(1) in locs:
                        pool.append((name, i.ir_line, i.line, locs[m.group(1)]))
    picked = rng.sample(pool, min(sample, len(pool)))
    bad = [p for p in picked if p[2] != p[3]]
    return not bad, f"{len(picked)} instruction(s) sampled, {len(bad)} line mismatch(es)"


# --------------------------------------------------------------------- A3.6
def mutation_run(name: str, cfg, z3: str, limit: int) -> tuple[int, list, int, int]:
    """Mutate the target's C sources and check that some gate notices (G7, §8.1).

    Two kinds of mutation cannot be killed and are counted apart, the way A1.2 counts
    the equivalent rule mutations:

      * one outside the code this target executes — the trace comes out byte for byte
        the same;
      * one the pre-condition hides. `for (i = 0; i < 4; i++)` becoming `i < 5` is the
        clean example: the fifth iteration reads bit 4 of a multiplier the pre-condition
        keeps below 16, so it adds nothing. Established by running both traces on the
        same pre-condition-satisfying inputs and comparing every snapshot."""
    t = targets.load(name)
    base_fe = built_frontend(name, cfg)
    executed = {o["function"] for o in base_fe.trace.origins.values() if "function" in o}
    mutants = []
    per_file = max(1, -(-limit // max(1, len(t.files))))
    for source in t.files:                   # every file the target compiles, not just one
        text = (t.vendor / source).read_text()
        mutants += g7.mutate_source(text, source, per_file,
                                    g7.function_lines(text, executed) or None)
    mutants = mutants[:limit]
    baseline = str(base_fe.trace.prog)
    runs = gates.runs(base_fe.trace, base_fe.spec, 40, seed=7)
    vectors = [_vector(base_fe.trace, values) for values, _ in runs]
    base_out = [g2.trace_snapshots(base_fe.trace, v) for v in vectors]

    killed, survived, equivalent = 0, [], 0
    for m in mutants:
        work = WORK / "mutants" / name / m.name.replace("/", "_")
        try:
            _, fe, build, out = build_target(name, cfg, mutate={m.path: m.text}, work=work)
        except Exception:
            killed += 1                      # the frontend or the spec check refused it
            continue
        if str(fe.trace.prog) == baseline:
            equivalent += 1
            continue
        try:
            runs = gates.runs(fe.trace, fe.spec, 40, seed=7)
        except RuntimeError:
            killed += 1                      # no input satisfies the precondition any more
            continue
        bad4, _ = g4.check_runs(fe.trace, fe.spec, runs)
        if bad4:
            killed += 1
            continue
        if g5.check(sorted(out.glob("*.range.smt2")), z3):
            killed += 1
            continue
        mix = [out / f"cut{vc.index}.smt2" for vc in build.vcs]
        bad6, _ = g6.check(mix, cfg, out / "_runs", timeout=120)
        if bad6:
            killed += 1
        elif _same_behaviour(fe.trace, vectors, base_out):
            equivalent += 1
        else:
            survived.append(f"{m.name} ({m.description})")
    return killed, survived, len(mutants), equivalent


def _vector(trace, values: dict) -> dict:
    """A G4 sample, rewritten as the registered-object vector G2 speaks."""
    out = {}
    for obj, cells in g2.input_objects(trace).items():
        out[obj] = [values[cells[i]] for i in sorted(cells)]
    return out


def _same_behaviour(trace, vectors: list, base_out: list) -> bool:
    """Does the mutant compute the same thing on inputs the pre-condition allows?"""
    try:
        return [g2.trace_snapshots(trace, v) for v in vectors] == base_out
    except KeyError:
        return False                         # it no longer has the same objects


_FRONTENDS: dict = {}


def built_frontend(name: str, cfg):
    if name not in _FRONTENDS:
        _FRONTENDS[name] = targets.prepare(targets.load(name), WORK / name)
    return _FRONTENDS[name]


# ----------------------------------------------------------------- A3.7/A3.8
def reject_run(src: Path, work: Path) -> tuple[str, str, int]:
    """Compile and run one standalone C file through the frontend.
    Returns (error code or 'ok', where, number of output files written)."""
    work.mkdir(parents=True, exist_ok=True)
    tc = Toolchain()
    try:
        ll = tc.build_ir([src], work / "ir", includes=(ROOT / "include",))
    except Exception as e:
        return "E-COMPILE", str(e).splitlines()[0][:60], 0
    out_dir = work / "out"
    try:
        mod = llparse.parse(ll.read_text(), str(ll))
        execute.execute(mod, "c2mix_body", max_steps=2_000_000)
    except llparse.ParseError as e:
        return e.code, (f"line {e.source}" if e.source else f"ir:{e.line}"), _count(out_dir)
    except execute.ExecError as e:
        return e.code, (f"line {e.line}" if e.line else f"ir:{e.ir_line}"), _count(out_dir)
    return "ok", "", _count(out_dir)


def _count(d: Path) -> int:
    return len(list(d.glob("*"))) if d.exists() else 0


# --------------------------------------------------------------------- A3.5
def cv_comparison(built: dict, cfg, work: Path, systemd: bool = True) -> str:
    """Put c2mix's output beside the `cv` mix_0 for the same program: statement counts
    per section, and what `bin/main` says about each. Report only — that corpus is not
    confirmed correct (§2.1), so it cannot decide whether c2mix is right."""
    from c2mix.oracle import run_mix
    out = []
    for name, ref in CV_PAIRS.items():
        if name not in built:
            continue
        path = CV_REFERENCE / f"{ref}.mix_0.smt2"
        _, _, build, out_dir = built[name]
        mine = _sections((out_dir / "cut0.smt2").read_text())
        if not path.exists():
            out.append(f"{name}: no cv reference at {path}")
            continue
        theirs = _sections(path.read_text())
        try:
            r = run_mix(cfg, path, cfg.prepass_default, work / ref, use_systemd=systemd,
                        timeout=300)
            verdict = f"{r.result} ({r.solver_seconds}s)"
        except Exception as e:
            verdict = f"not run ({type(e).__name__})"
        out.append(f"{name}: c2mix {mine} vs cv {theirs}, cv bin/main {verdict}")
    return "; ".join(out) or "no reference available"


def _sections(text: str) -> dict:
    names = {"decl": "; variable declaration", "range": "; range precondition",
             "alg": "; algebraic precondition", "post": "; postcondition"}
    counts, current = {k: 0 for k in names}, None
    for line in text.splitlines():
        for key, marker in names.items():
            if line.startswith(marker):
                current = key
        if current and line.startswith("(assert"):
            counts[current] += 1
        if current == "decl" and line.startswith("(declare-const"):
            counts["decl"] += 1
    return counts


# -------------------------------------------------------------------- report
def report(rows, notes, stamp, names) -> None:
    out = ROOT / "reports" / f"accept-3-{stamp}.md"
    out.parent.mkdir(parents=True, exist_ok=True)
    overall = "PASS" if all(r[1] for r in rows) else "FAIL"
    lines = [f"# 第 3 階段驗收 — {stamp}", "", f"整體：**{overall}**", "",
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
