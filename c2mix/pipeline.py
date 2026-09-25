"""Trace + specification -> the files in out/<target>/ (spec §1.1, §7).

Phase 3 puts the C frontend in front of this; phase 2 hands it hand-written traces.
"""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from .emit import manifest as manifest_mod
from .emit import mix as mix_mod
from .emit import range as range_mod
from .ir.trace import Trace
from .spec import check as check_mod
from .spec import dsl
from .vc.assemble import Options, assemble


class SpecError(Exception):
    pass


@dataclass
class Build:
    vcs: list
    manifest: dict
    files: list[Path]
    out_dir: Path


def build(trace: Trace, target: dsl.Target, out_dir: str | Path, name: str = "target",
          opts: Options | None = None, cfg=None, range_split: int = 1,
          spec_source: str | None = None, frontend: dict | None = None) -> Build:
    opts = opts or Options()
    if range_split > 1 and not opts.range_slices:
        from dataclasses import replace
        opts = replace(opts, range_slices=True)
    failures = check_mod.check_spec(target, trace)
    if failures:
        raise SpecError("; ".join(str(f) for f in failures))

    z3 = cfg.data["solver"]["range"]["bin"] if cfg else "z3"
    vcs = assemble(trace, target, opts, z3_bin=z3)

    out_dir = Path(out_dir)
    files: list[Path] = []
    per_cut: dict[int, dict] = {}
    for vc in vcs:
        m = mix_mod.write(vc, out_dir / f"cut{vc.index}.smt2", opts.hints)
        r = range_mod.write(vc, out_dir / f"cut{vc.index}.range.smt2", range_split)
        files += [m] + r
        per_cut[vc.index] = {"mix": m.name, "range": [x.name for x in r]}
    stats = dict(frontend or {})
    if trace.origins:
        stats["origins"] = trace.origins
    man = manifest_mod.build(vcs, name, opts, cfg, per_cut, spec_source, stats)
    files.append(manifest_mod.write(man, out_dir / "manifest.json"))
    return Build(vcs, man, files, out_dir)
