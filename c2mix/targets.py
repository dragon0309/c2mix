"""Targets: `targets/<name>/` plus the vendored sources it names (spec §4.1).

A target is the only place scheme knowledge is allowed to live (G10). This module
turns one into a trace: copy the vendored sources into a work directory, apply the
cut patch there (the upstream files are never modified, §1.1), generate the harness,
run the frontend.
"""
from __future__ import annotations

import hashlib
import importlib
import re
import shutil
import sys
import tomllib
from dataclasses import dataclass
from pathlib import Path

from .config import ROOT
from .frontend import execute, harness, llparse
from .frontend.toolchain import Toolchain
from .spec import dsl


class TargetError(Exception):
    pass


@dataclass
class Target:
    name: str
    path: Path
    data: dict
    root: Path

    @property
    def entry(self) -> str:
        return self.data["source"]["entry"]

    @property
    def mode(self) -> str:
        return self.data.get("build", {}).get("mode", "include")

    @property
    def defines(self) -> list[str]:
        return list(self.data.get("build", {}).get("defines", []))

    @property
    def vendor(self) -> Path:
        return self.root / "vendor" / self.data["source"].get("vendor", self.name)

    @property
    def files(self) -> list[str]:
        return list(self.data["source"].get("files", []))

    @property
    def max_steps(self) -> int:
        return int(self.data.get("limits", {}).get("max_steps", execute.MAX_STEPS))

    @property
    def max_merge_depth(self) -> int:
        return int(self.data.get("limits", {}).get("max_merge_depth",
                                                   execute.MAX_MERGE_DEPTH))

    @property
    def must_pass(self) -> bool:
        return bool(self.data.get("expect", {}).get("must_pass", True))

    @property
    def signed_override(self) -> dict:
        return dict(self.data.get("build", {}).get("signed", {}))

    def variant_patch(self, variant: str | None) -> Path | None:
        if variant:
            name = self.data.get("variants", {}).get(variant)
            if name is None:
                raise TargetError(f"{self.name}: no variant {variant!r}")
            return self.path / name
        p = self.path / "cuts.patch"
        return p if p.exists() and p.read_text().strip() else None

    def spec(self) -> dsl.Target:
        if str(self.root) not in sys.path:
            sys.path.insert(0, str(self.root))
        mod = importlib.import_module(f"targets.{self.name}.spec")
        importlib.reload(mod)
        return mod.build()


def load(name: str, root: Path | None = None) -> Target:
    root = root or ROOT
    path = root / "targets" / name
    toml = path / "target.toml"
    if not toml.exists():
        raise TargetError(f"no target {name!r} at {path}")
    with open(toml, "rb") as fh:
        return Target(name, path, tomllib.load(fh), root)


def names(root: Path | None = None) -> list[str]:
    root = root or ROOT
    d = root / "targets"
    return sorted(p.name for p in d.iterdir()
                  if (p / "target.toml").exists()) if d.exists() else []


# ------------------------------------------------------------------- patching
HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def apply_patch(patch_text: str, work: Path) -> list[str]:
    """Apply a unified diff to files under `work`. Small and strict on purpose: a
    cut patch that no longer applies must fail loudly, not half-apply."""
    touched, lines, i = [], patch_text.splitlines(), 0
    while i < len(lines):
        if not lines[i].startswith("--- "):
            i += 1
            continue
        target = lines[i + 1][4:].split("\t")[0].strip()
        target = target.split("/", 1)[1] if target.startswith(("b/", "a/")) else target
        path = work / target
        if not path.exists():
            raise TargetError(f"patch target {target} does not exist")
        src = path.read_text().splitlines()
        out, cursor, i = [], 0, i + 2
        while i < len(lines) and not lines[i].startswith("--- "):
            m = HUNK.match(lines[i])
            if not m:
                i += 1
                continue
            start = int(m.group(1)) - 1
            out += src[cursor:start]
            cursor = start
            i += 1
            while i < len(lines) and lines[i][:1] in (" ", "-", "+", "\\"):
                mark, text = lines[i][0], lines[i][1:]
                if mark == " ":
                    if src[cursor] != text:
                        raise TargetError(f"{target}:{cursor + 1}: context does not match:\n"
                                          f"  file:  {src[cursor]!r}\n  patch: {text!r}")
                    out.append(text)
                    cursor += 1
                elif mark == "-":
                    if src[cursor] != text:
                        raise TargetError(f"{target}:{cursor + 1}: removed line does not match")
                    cursor += 1
                elif mark == "+":
                    out.append(text)
                i += 1
        out += src[cursor:]
        path.write_text("\n".join(out) + "\n")
        touched.append(target)
    if not touched:
        raise TargetError("the patch changed nothing")
    return touched


# ------------------------------------------------------------------ the frontend
@dataclass
class Frontend:
    trace: object
    stats: dict
    module: llparse.Module
    ll: Path
    harness: Path
    work: Path
    spec: dsl.Target
    objects: list


def prepare(t: Target, work: Path, variant: str | None = None,
            tc: Toolchain | None = None, mutate: dict | None = None) -> Frontend:
    """Everything up to the trace: sources -> harness -> IR -> execution.

    `mutate` maps a file name to replacement text, applied to the work copy after the
    cut patch: that is how G7 builds a mutant without touching the vendored source."""
    tc = tc or Toolchain()
    work.mkdir(parents=True, exist_ok=True)
    src_dir = work / "src"
    if src_dir.exists():
        shutil.rmtree(src_dir)
    src_dir.mkdir(parents=True)
    for f in t.files:
        shutil.copy2(t.vendor / f, src_dir / Path(f).name)
    for extra in t.vendor.glob("*.h"):
        if not (src_dir / extra.name).exists():
            shutil.copy2(extra, src_dir / extra.name)
    patch = t.variant_patch(variant)
    if patch is not None:
        apply_patch(patch.read_text(), src_dir)
    for name, text in (mutate or {}).items():
        (src_dir / name).write_text(text)

    spec = t.spec()
    objs = harness.objects(spec, t.signed_override)
    names_ = [Path(f).name for f in t.files]
    text = harness.generate(
        spec, t.entry, objs, defines=t.defines,
        includes=names_ if t.mode == "include" else [],
        declares=[] if t.mode == "include" else _declarations(t, src_dir))
    hpath = src_dir / "harness.c"
    hpath.write_text(text)

    sources = [hpath] + ([] if t.mode == "include"
                         else [src_dir / n for n in names_])
    ll = tc.build_ir(sources, work / "ir", includes=(t.root / "include", src_dir))
    mod = llparse.parse(ll.read_text(), str(ll))
    trace, stats = execute.execute(mod, t.entry, t.max_steps, t.max_merge_depth)
    stats["variant"] = variant or "default"
    stats["entry"] = t.entry
    stats["commit"] = t.data["source"].get("commit")
    stats["sources"] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()[:16]
                        for p in sorted(src_dir.iterdir()) if p.suffix in (".c", ".h")}
    return Frontend(trace, stats, mod, ll, hpath, work, spec, objs)


def native(t: Target, fe: Frontend, opt: str = "-O0",
           tc: Toolchain | None = None) -> Path:
    """G2's native binary: the same program.m2r.ll, plus the runtime."""
    tc = tc or Toolchain()
    out = fe.work / f"native{opt}"
    return tc.build_native(fe.ll, [t.root / "runtime" / "c2mix_rt.c"], out,
                           includes=(t.root / "include",), opt=opt)


def _declarations(t: Target, src_dir: Path) -> list[str]:
    """link mode: the harness only needs the entry's prototype, taken from the header
    the target lists."""
    out = []
    for h in t.data.get("build", {}).get("headers", []):
        out.append(f'#include "{Path(h).name}"')
    return out
