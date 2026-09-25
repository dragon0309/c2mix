"""c2mix command line (spec §10.1)."""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

from . import config


def _expand(paths: list[str]) -> list[Path]:
    out: list[Path] = []
    for p in map(Path, paths):
        out += sorted(p.glob("*.smt2"), key=config._natural) if p.is_dir() else [p]
    return out


def _key(cfg: config.Config, f: Path) -> str:
    """Baseline key: path relative to the golden root when under it."""
    try:
        return f.resolve().relative_to(cfg.golden_root).as_posix()
    except ValueError:
        return f.as_posix()


def cmd_lint(args) -> int:
    from .mixfmt import lint
    cfg = config.load(args.config)
    files = _expand(args.files)
    results: dict[str, dict[str, int]] = {}
    n_err = 0
    for f in files:
        key = _key(cfg, f)
        diags = lint.lint_file(f, args.profile, cfg if args.z3 else None, display=str(f))
        errs = [d for d in diags if d.severity == lint.E]
        n_err += len(errs)
        results[key] = lint.summarize(diags)
        shown = errs if args.quiet else diags
        for d in shown[:args.max_per_file] if args.max_per_file else shown:
            print(d.render())
        if args.max_per_file and len(shown) > args.max_per_file:
            print(f"{f}: … {len(shown) - args.max_per_file} more")
        print(f"{f}: {len(errs)} error(s), warnings {results[key] or '{}'}")
    status = 0
    if n_err:
        print(f"lint: {n_err} error(s) in {len(files)} file(s)")
        status = 1
    if args.write_baseline:
        lint.dump_baseline(args.write_baseline, args.profile, results)
        print(f"lint: wrote baseline {args.write_baseline}")
    if args.baseline:
        base = lint.load_baseline(args.baseline)
        if base.get("profile") != args.profile:
            print(f"lint: baseline profile is {base.get('profile')}, not {args.profile}")
            status = 1
        want = base["files"]
        for key in sorted(set(want) | set(results)):
            if key not in results:
                print(f"baseline: {key} is in the baseline but was not linted")
                status = 1
            elif key not in want:
                print(f"baseline: {key} is not in the baseline")
                status = 1
            elif want[key] != results[key]:
                print(f"baseline: {key} warnings differ: expected {want[key]}, got {results[key]}")
                status = 1
        print("lint: warnings match baseline" if status == 0 else "lint: FAILED")
    return status


def cmd_roundtrip(args) -> int:
    from .mixfmt import reader, writer
    cfg = config.load(args.config)
    files = _expand(args.files)
    outdir = Path(args.output) if args.output else None
    status = 0
    written: list[tuple[Path, Path]] = []
    for f in files:
        src = f.read_text(encoding="utf-8")
        out = writer.write(reader.parse(src, str(f)))
        same_norm = writer.normalize(out) == writer.normalize(src)
        same_bytes = out == src
        print(f"{f}: normalized {'OK' if same_norm else 'DIFF'}, bytes {'identical' if same_bytes else 'differ'}")
        status |= 0 if same_norm else 1
        if outdir:
            key = Path(_key(cfg, f))
            if key.is_absolute() or ".." in key.parts:
                key = Path(f.name)          # never let the output path escape outdir
            dst = outdir / key
            if dst.resolve() == f.resolve():
                print(f"roundtrip: refusing to overwrite the input {f}")
                return 2
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(out, encoding="utf-8")
            written.append((f, dst))
    if args.solve:
        from .oracle import run_mix
        if not outdir:
            print("roundtrip: --solve needs -o")
            return 2
        for orig, dst in written:
            prepass = args.prepass or cfg.golden_needs_prepass(orig)
            r = run_mix(cfg, dst, prepass, outdir / "_runs", use_systemd=not args.no_systemd)
            ok = r.result == args.expect
            status |= 0 if ok else 1
            print(f"{dst}: bin/main {r.result} ({r.solver_seconds}s, prepass={prepass}) "
                  f"{'OK' if ok else 'FAIL expected ' + args.expect}  log {r.log}")
    print("roundtrip: OK" if status == 0 else "roundtrip: FAILED")
    return status


def cmd_lemmas(args) -> int:
    """A1.1/A1.2: generate the rule lemmas (and mutants) and optionally check them."""
    from .lower import lemmas
    widths = tuple(int(w) for w in args.widths.split(",")) if args.widths else lemmas.LEMMA_WIDTHS
    base = lemmas.generate(widths)
    items: list = []
    for L in base:
        variants = []
        if args.variant in ("mixed", "both"):
            variants.append(L)
        if args.variant in ("bv", "both"):
            variants.append(lemmas.render_bv(L))
        items += variants
        if args.mutants:
            for m in lemmas.mutate(L):
                items.append(m if args.variant == "mixed" else lemmas.render_bv(m))
    if args.out:
        out = Path(args.out)
        out.mkdir(parents=True, exist_ok=True)
        for L in items:
            (out / f"{L.name}.{L.variant}.smt2").write_text(L.text)
        print(f"lemmas: wrote {len(items)} files to {out}")
    if not args.check:
        return 0
    cfg = config.load(args.config)
    z3 = cfg.data["solver"]["range"]["bin"]
    results = lemmas.check_all(items, z3, jobs=args.jobs, timeout=args.timeout)
    bad = [(L, got) for L, ok, got in results if not ok]
    eq = [L for L, ok, _ in results if L.equivalent]
    for L, got in bad:
        print(f"{L.name} [{L.variant}]: expected {L.expect}, got {got}")
    print(f"lemmas: {len(items)} checked, {len(bad)} failed, {len(eq)} equivalent mutations")
    return 1 if bad else 0


def cmd_build(args) -> int:
    """C sources + specification -> out/<target>/ (spec §10.1)."""
    from . import pipeline, targets
    from .vc.assemble import Options
    cfg = config.load(args.config)
    t = targets.load(args.target)
    work = Path(args.work) if args.work else config.ROOT / "work" / "build" / args.target
    fe = targets.prepare(t, work, args.variant)
    out = Path(args.output) if args.output else config.ROOT / "out" / args.target
    opts = Options(int_encoding=args.int_encoding, ghost=args.ghost,
                   exactness=args.exactness, hints=args.hints, carry=args.carry)
    build = pipeline.build(fe.trace, fe.spec, out, args.target, opts, cfg,
                           range_split=args.range_split or t.range_split,
                           spec_source=str(t.path / "spec.py"))
    print(f"{args.target}: {len(build.vcs)} cut(s), {fe.stats['instructions']} IR instructions, "
          f"{fe.stats['steps']} steps, {fe.stats['merges']} merge(s)")
    for f in build.files:
        print(f"  {f}")
    return 0


def cmd_gate(args) -> int:
    """Run one gate on a target (spec §10.1: `c2mix gate G<n> <target>`)."""
    from . import gates as gates_pkg
    from . import pipeline, targets
    from .gates import g1, g2, g3, g4, g5, g6, g8, g9
    from .vc.assemble import Options
    cfg = config.load(args.config)
    t = targets.load(args.target)
    work = Path(args.work) if args.work else config.ROOT / "work" / "gate" / args.target
    fe = targets.prepare(t, work, args.variant)
    out = work / "out"
    build = pipeline.build(fe.trace, fe.spec, out, args.target,
                           Options(hints=args.hints), cfg)
    mix = [out / f"cut{vc.index}.smt2" for vc in build.vcs]
    rng = sorted(out.glob("*.range.smt2"))
    name = args.gate.upper()
    if name == "G1":
        bad, warn = g1.check(mix + rng, "consumer", cfg)
        print(f"G1 warnings: {warn}")
    elif name == "G2":
        binary = targets.native(t, fe)
        vecs, exhaustive = g2.vectors(fe.trace, args.runs)
        rep = g2.check(fe.trace, binary, vecs, work / "g2")
        print(f"G2: {len(vecs)} vector(s){' (exhaustive)' if exhaustive else ''}, "
              f"{rep.compared} element(s) compared")
        bad = rep.mismatches
    elif name in ("G3", "G4"):
        runs = gates_pkg.runs(fe.trace, fe.spec, args.runs)
        bad = (g3.check_runs(build.vcs, fe.trace, fe.spec, runs) if name == "G3"
               else g4.check_runs(fe.trace, fe.spec, runs)[0])
    elif name == "G5":
        bad = g5.check(rng, cfg.data["solver"]["range"]["bin"])
    elif name == "G6":
        bad, _ = g6.check(mix, cfg, out / "_runs")
    elif name == "G8":
        first = g8.digest(build.files)
        again = pipeline.build(fe.trace, fe.spec, work / "out2", args.target,
                               Options(hints=args.hints), cfg)
        bad = g8.compare(first, g8.digest(again.files))
    elif name == "G9":
        bad = g9.check(build.manifest)
    else:
        print(f"gate: {args.gate} is not one that runs per target "
              "(G7 is the mutation gate, G10 is a grep over the core)")
        return 2
    for line in bad:
        print(line)
    print(f"{name} {args.target}: {'PASS' if not bad else 'FAIL'}")
    return 0 if not bad else 1


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="c2mix")
    ap.add_argument("--config", help="c2mix.toml (default: next to the package)")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("lint", help="check mix files against the format contract (§7.3)")
    p.add_argument("--profile", choices=("strict", "consumer"), default="strict")
    p.add_argument("--baseline", help="JSON baseline: warnings must match it exactly")
    p.add_argument("--write-baseline", metavar="FILE", help="write the observed warnings as a baseline")
    p.add_argument("--z3", action="store_true", help="also parse each file with z3 (rule PARSE)")
    p.add_argument("-q", "--quiet", action="store_true", help="print errors and per-file summaries only")
    p.add_argument("--max-per-file", type=int, default=0, help="limit printed diagnostics per file")
    p.add_argument("files", nargs="+")
    p.set_defaults(fn=cmd_lint)

    p = sub.add_parser("roundtrip", help="check write(read(f)) == f after normalization")
    p.add_argument("-o", "--output", help="directory for the rewritten files")
    p.add_argument("--solve", action="store_true", help="run bin/main on the rewritten files")
    p.add_argument("--expect", default="unsat", help="expected bin/main result (default unsat)")
    p.add_argument("--prepass", action="store_true", help="force the partition prepass flags")
    p.add_argument("--no-systemd", action="store_true", help="do not wrap bin/main in systemd-run")
    p.add_argument("files", nargs="+")
    p.set_defaults(fn=cmd_roundtrip)

    p = sub.add_parser("lemmas", help="rule lemmas A1.1 and their mutations A1.2")
    p.add_argument("--out", help="directory to write the .smt2 files to")
    p.add_argument("--check", action="store_true", help="run z3 on them")
    p.add_argument("--variant", choices=("mixed", "bv", "both"), default="both",
                   help="mixed: the encoding c2mix emits; bv: its QF_BV image")
    p.add_argument("--widths", help="comma separated (default 4,8,16,32,64)")
    p.add_argument("--mutants", action="store_true", help="also generate the A1.2 mutations")
    p.add_argument("--jobs", type=int, default=8)
    p.add_argument("--timeout", type=float, default=60)
    p.set_defaults(fn=cmd_lemmas)

    p = sub.add_parser("build", help="C sources + spec -> out/<target>/ (§10.1)")
    p.add_argument("target")
    p.add_argument("--variant", help="a cut granularity from [variants] in target.toml")
    p.add_argument("-o", "--output", help="output directory (default out/<target>)")
    p.add_argument("--work", help="scratch directory (default work/build/<target>)")
    p.add_argument("--hints", choices=("emit", "omit"), default="omit")
    p.add_argument("--int-encoding", choices=("alias", "bv2int"), default="alias")
    p.add_argument("--ghost", choices=("bind", "inline", "legacy-pow2"), default="bind")
    p.add_argument("--exactness", choices=("auto", "split"), default="auto")
    p.add_argument("--carry", choices=("relevant", "previous", "all"), default="relevant")
    p.add_argument("--range-split", type=int, default=None,
                   help="files per range VC (default: the target's, else 1)")
    p.set_defaults(fn=cmd_build)

    p = sub.add_parser("gate", help="run one gate on a target (§10.1)")
    p.add_argument("gate", help="G1 … G9")
    p.add_argument("target")
    p.add_argument("--variant")
    p.add_argument("--work")
    p.add_argument("--hints", choices=("emit", "omit"), default="emit")
    p.add_argument("--runs", type=int, default=1000, help="G2/G3/G4 sample size")
    p.set_defaults(fn=cmd_gate)

    args = ap.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
