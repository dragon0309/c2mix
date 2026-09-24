"""Loads c2mix.toml. Relative paths are resolved against the file's directory."""
from __future__ import annotations

import tomllib
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


@dataclass
class Config:
    data: dict
    root: Path

    def path(self, value: str) -> Path:
        p = Path(value)
        return p if p.is_absolute() else (self.root / p).resolve()

    @property
    def golden_root(self) -> Path:
        return self.path(self.data["golden"]["root"])

    def golden_files(self) -> list[Path]:
        files = []
        for s in self.data["golden"]["sets"]:
            files += sorted((self.golden_root / s).glob("*.smt2"), key=_natural)
        return files

    def golden_set(self, f: Path) -> str | None:
        f = Path(f).resolve()
        for s in self.data["golden"]["sets"]:
            if f.parent == (self.golden_root / s).resolve():
                return s
        return None

    @property
    def prepass_default(self) -> bool:
        return bool(self.data["solver"]["mix"].get("prepass_default", False))

    def mix_flags(self, prepass: bool) -> list[str]:
        m = self.data["solver"]["mix"]
        return list(m["common"]) + (list(m["omit_extra"]) if prepass else [])

    def golden_needs_prepass(self, f: Path) -> bool:
        return self.golden_set(f) in self.data["golden"].get("prepass", [])


def _natural(p: Path):
    import re
    return [int(t) if t.isdigit() else t for t in re.split(r"(\d+)", p.name)]


def load(path: str | Path | None = None) -> Config:
    path = Path(path) if path else ROOT / "c2mix.toml"
    with open(path, "rb") as fh:
        return Config(tomllib.load(fh), path.resolve().parent)
