#!/usr/bin/env python3
"""A0.4 encoding A/B on the signed/polynomial golden set (spec §9, phase 0).

1. Integer encoding (D4): every file of the set as-is (bv2int) and converted to the
   alias encoding with extend_z3's working/cbmc_small/signed_alias.py; same bin/main
   flags for both. Records result, time and MaxRSS.
2. Ghost form (D8) on the entry cut (ghost bound there) and the next cut (ghost only
   in the precondition and the goal):
     legacy-pow2  (eqP (PPow g 2) F) as in the golden
     bind         (eqP g F); every (PPow g 2) becomes g
     inline       no ghost symbol; every (PPow g 2) becomes F, F's inputs declared
   run under the alias encoding (and, with --ghost-bv2int, also under bv2int).

Nothing outside the c2mix tree is written: transformed files go to work/a0.4/,
bin/main runs in per-run directories under work/a0.4/runs/.

usage: tests/phase0/ab_encoding.py [--set NAME] [--only-ghost] [--ghost-bv2int]
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from c2mix import config, oracle  # noqa: E402
from c2mix.mixfmt import lint, reader, writer  # noqa: E402
from c2mix.mixfmt.reader import Command  # noqa: E402

WORK = ROOT / "work" / "a0.4"
SIGNED_ALIAS = "../extend_z3/working/cbmc_small/signed_alias.py"
F6_TOTAL_S = 185.19                      # spec F6, 2026-08-23, 15 files


# ------------------------------------------------------------------ ghost transforms
def ghost_symbols(mix) -> list[str]:
    return [c.sexpr[1] for c in mix.commands()
            if c.head == "declare-const" and c.sexpr[2] == ["Poly", "Int"]]


def find_binding(mix, g):
    """The golden entry cut binds the ghost with (assert (eqP (PPow g 2) F))."""
    for c in mix.commands():
        s = c.sexpr
        if (c.head == "assert" and isinstance(s[1], list) and len(s[1]) == 3
                and s[1][0] == "eqP" and s[1][1] == ["PPow", g, "2"]):
            return c, s[1][2]
    return None, None


def check_only_pow2(mix, g):
    """Every use of g (outside its declaration) must be (PPow g 2)."""
    for c in mix.commands():
        if c.head == "declare-const":
            continue
        uses = sum(1 for a in reader.atoms(c.sexpr) if a == g)
        pow2 = sum(1 for n in reader.iter_nodes(c.sexpr) if n == ["PPow", g, "2"])
        if uses != pow2:
            raise SystemExit(f"{g} used outside (PPow {g} 2) at line {c.line}")


def ghost_transform(mix, form: str, source=None):
    """Return a new MixFile with the ghost rewritten to `form`.
    `source` is the entry-cut MixFile (to take F from when mix has no binding)."""
    if form == "legacy-pow2":
        return mix
    gs = ghost_symbols(mix)
    if len(gs) != 1:
        raise SystemExit(f"expected exactly one ghost, found {gs}")
    g = gs[0]
    check_only_pow2(mix, g)
    pow2 = ["PPow", g, "2"]
    items = list(mix.items)
    if form == "bind":
        repl = g
    elif form == "inline":
        bind_cmd, F = find_binding(mix, g)
        if bind_cmd is None:
            if source is None:
                raise SystemExit("inline needs the entry cut as source")
            _, F = find_binding(source, g)
            src_decl = {c.sexpr[1]: c for c in source.commands() if c.head == "declare-const"}
            have = {c.sexpr[1] for c in mix.commands() if c.head == "declare-const"}
            need = sorted({a for a in reader.atoms(F) if a in src_decl and a not in have})
            last_decl = max(i for i, it in enumerate(items)
                            if isinstance(it, Command) and it.head == "declare-const")
            items[last_decl + 1:last_decl + 1] = [Command(src_decl[n].sexpr, 0) for n in need]
        else:
            items = [it for it in items if it is not bind_cmd]
        items = [it for it in items
                 if not (isinstance(it, Command) and it.head == "declare-const" and it.sexpr[1] == g)]
        repl = F
    else:
        raise ValueError(form)
    out = []
    for it in items:
        if isinstance(it, Command):
            it = Command(reader.rewrite(it.sexpr, lambda n: repl if n == pow2 else None), it.line)
        out.append(it)
    return reader.MixFile(out, mix.path)


def mutate_goal_modulus(mix):
    """Discrimination check: in the goal, change the constant c of the first modulus
    (PSub (PPow x k) (PConst c)) to c + 1. The result must not be unsat."""
    items = list(mix.items)
    i = max(k for k, it in enumerate(items) if isinstance(it, Command) and it.head == "assert")
    done = []

    def fn(n):
        if (not done and isinstance(n, list) and len(n) == 3 and n[0] == "PSub"
                and isinstance(n[1], list) and n[1][:1] == ["PPow"]
                and isinstance(n[2], list) and n[2][0] == "PConst" and n[2][1].isdigit()):
            done.append(n[2][1])
            return ["PSub", n[1], ["PConst", str(int(n[2][1]) + 1)]]
        return None
    items[i] = Command(reader.rewrite(items[i].sexpr, fn), items[i].line)
    if not done:
        raise SystemExit("no (PSub (PPow x k) (PConst c)) modulus in the goal")
    return reader.MixFile(items, mix.path), done[0]


# ------------------------------------------------------------------ runs
def to_alias(cfg, src: Path, dst: Path):
    dst.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run([sys.executable, str(cfg.path(SIGNED_ALIAS)), str(src), str(dst)], check=True)


def _rel(p) -> str:
    return os.path.relpath(p, ROOT)


def solve(cfg, f: Path, tag: str, args, timeout=None) -> dict:
    r = oracle.run_mix(cfg, f, True, WORK / "runs" / tag, use_systemd=not args.no_systemd,
                       timeout=timeout or args.timeout)
    errs = [d for d in lint.lint_file(f, "consumer") if d.severity == lint.E]
    row = {"tag": tag, "file": _rel(f), "result": r.result, "exit": r.exit_code,
           "solver_s": r.solver_seconds, "wall_s": round(r.wall_seconds, 2),
           "maxrss_kib": r.maxrss_kib, "lint_errors": len(errs), "log": _rel(r.log)}
    t = f"{r.solver_seconds}s" if r.solver_seconds is not None else f"wall {r.wall_seconds:.0f}s"
    rss = f" rss={r.maxrss_kib}KiB" if r.maxrss_kib is not None else ""
    print(f"  {tag:28s} {f.name:14s} {r.result:8s} {t}{rss}", flush=True)
    return row


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--set", default="pqclean_kyber768_avx2_noAssume")
    ap.add_argument("--entry", default="cut0.smt2", help="cut where the ghost is bound")
    ap.add_argument("--next", default="cut1.smt2", help="cut where the ghost is only in pre/goal")
    ap.add_argument("--only-ghost", action="store_true")
    ap.add_argument("--ghost-bv2int", action="store_true", help="also run ghost forms under bv2int")
    ap.add_argument("--no-systemd", action="store_true")
    ap.add_argument("--timeout", type=float, default=3600)
    ap.add_argument("--sanity", action="store_true",
                    help="only the discrimination check: mutated goals of the next cut must not be unsat")
    ap.add_argument("--sanity-timeout", type=float, default=300)
    ap.add_argument("--report-only", metavar="RESULTS_JSON", help="rebuild the report from saved results")
    args = ap.parse_args()

    cfg = config.load()
    if args.report_only:
        f = Path(args.report_only)
        report(json.loads(f.read_text()), f.stem.removeprefix("results-"), cfg)
        return
    gdir = cfg.golden_root / args.set
    files = sorted(gdir.glob("*.smt2"), key=config._natural)
    rows = []

    if args.sanity:
        print("== sanity: mutated goal modulus (expect not unsat)", flush=True)
        for form in ("legacy-pow2", "bind", "inline"):
            a = WORK / "ghost" / f"{form}.alias" / args.next
            if not a.exists():
                raise SystemExit(f"{a} missing: run the ghost step first")
            mut, c = mutate_goal_modulus(reader.read(a))
            m = WORK / "sanity" / f"{form}.alias.{Path(args.next).stem}.mut.smt2"
            m.parent.mkdir(parents=True, exist_ok=True)
            writer.write_file(mut, m)
            row = solve(cfg, m, f"sanity-{form}/alias", args, timeout=args.sanity_timeout)
            row["note"] = f"goal modulus constant {c} -> {int(c) + 1}; timeout {args.sanity_timeout:g}s"
            rows.append(row)
        args.only_ghost = True
        files = []

    if not args.only_ghost:
        print("== D4: integer encoding", flush=True)
        for f in files:
            rows.append(solve(cfg, f, "bv2int", args))
            a = WORK / "alias" / f.name
            to_alias(cfg, f, a)
            rows.append(solve(cfg, a, "alias", args))

    print("== D8: ghost form", flush=True)
    entry = reader.read(gdir / args.entry)
    for name in (() if args.sanity else (args.entry, args.next)):
        mix = reader.read(gdir / name)
        for form in ("legacy-pow2", "bind", "inline"):
            g = WORK / "ghost" / f"{form}.bv2int" / name
            g.parent.mkdir(parents=True, exist_ok=True)
            writer.write_file(ghost_transform(mix, form, entry), g)
            a = WORK / "ghost" / f"{form}.alias" / name
            to_alias(cfg, g, a)
            rows.append(solve(cfg, a, f"ghost-{form}/alias", args))
            if args.ghost_bv2int:
                rows.append(solve(cfg, g, f"ghost-{form}/bv2int", args))

    WORK.mkdir(parents=True, exist_ok=True)
    stamp = datetime.date.today().isoformat()
    out = WORK / f"results-{stamp}.json"
    prev = json.loads(out.read_text()) if out.exists() else []
    keep = [r for r in prev if (r["tag"], r["file"]) not in {(x["tag"], x["file"]) for x in rows}]
    out.write_text(json.dumps(keep + rows, indent=1) + "\n")
    print(f"results: {out}")
    report(keep + rows, stamp, cfg)


def report(rows, stamp, cfg):
    from accept import solver_fingerprint
    def total(tag):
        rs = [r for r in rows if r["tag"] == tag]
        return rs, sum(r["solver_s"] or 0 for r in rs), max((r["maxrss_kib"] or 0) for r in rs) if rs else 0

    lines = [f"# A0.4 編碼 A/B — {stamp}", "",
             "由 `tests/phase0/ab_encoding.py` 產生。flag：`c2mix.toml` 的 common + omit_extra（partition prepass）。",
             "時間是 bin/main 回報的 `Verification result` 秒數；MaxRSS 取 bin/main 回報的 self 與 gb-worker-max 的較大者。",
             f"bin/main：{solver_fingerprint(cfg)}。", ""]
    b, tb, mb = total("bv2int")
    a, ta, ma = total("alias")
    if b or a:
        lines += ["## D4：bv2int vs alias", "",
                  "| 檔案 | bv2int | 秒 | MaxRSS KiB | alias | 秒 | MaxRSS KiB |", "|---|---|---:|---:|---|---:|---:|"]
        by = {}
        for r in b + a:
            by.setdefault(Path(r["file"]).name, {})[r["tag"]] = r
        for name in sorted(by, key=lambda n: config._natural(Path(n))):
            x, y = by[name].get("bv2int", {}), by[name].get("alias", {})
            lines.append(f"| {name} | {x.get('result', '')} | {x.get('solver_s', '')} | {x.get('maxrss_kib', '')} "
                         f"| {y.get('result', '')} | {y.get('solver_s', '')} | {y.get('maxrss_kib', '')} |")
        lines += [f"| **合計** | {sum(r['result'] == 'unsat' for r in b)}/{len(b)} unsat | {tb:.2f} | {mb} "
                  f"| {sum(r['result'] == 'unsat' for r in a)}/{len(a)} unsat | {ta:.2f} | {ma} |", "",
                  f"F6 基準（2026-08-23）：{F6_TOTAL_S} s。", ""]
    g = [r for r in rows if r["tag"].startswith("ghost-")]
    if g:
        lines += ["## D8：ghost 形式", "", "| 形式 | 檔案 | 結果 | 秒 | MaxRSS KiB |", "|---|---|---|---:|---:|"]
        for r in g:
            lines.append(f"| {r['tag'][6:]} | {Path(r['file']).name} | {r['result']} | {r['solver_s']} | {r['maxrss_kib']} |")
        lines.append("")
    s = [r for r in rows if r["tag"].startswith("sanity-")]
    if s:
        lines += ["## 鑑別力檢查", "",
                  "把 next cut 目標裡第一個模數 x^k − c 的 c 改成 c + 1，結果不得為 `unsat`"
                  "（否則上面的 `unsat` 可能是前提矛盾造成的 vacuous 結果）。", "",
                  "| 形式 | 結果 | 牆鐘秒 | 判定 | 說明 |", "|---|---|---:|---|---|"]
        for r in s:
            lines.append(f"| {r['tag'][7:]} | {r['result']} | {r['wall_s']} | "
                         f"{'PASS' if r['result'] != 'unsat' else 'FAIL'} | {r.get('note', '')} |")
        lines.append("")
    path = ROOT / "reports" / f"a0.4-{stamp}.md"
    path.parent.mkdir(exist_ok=True)
    path.write_text("\n".join(lines) + "\n")
    print(f"report: {path}")


if __name__ == "__main__":
    main()
