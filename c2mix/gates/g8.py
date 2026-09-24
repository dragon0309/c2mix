"""G8 — determinism (M9): building twice gives byte-identical files."""
from __future__ import annotations

import hashlib
from pathlib import Path


def digest(paths) -> dict[str, str]:
    return {Path(p).name: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths}


def compare(first: dict[str, str], second: dict[str, str]) -> list[str]:
    bad = [f"{n} missing from the second build" for n in first if n not in second]
    bad += [f"{n} only in the second build" for n in second if n not in first]
    bad += [f"{n} differs between builds" for n in first if n in second and first[n] != second[n]]
    return bad
