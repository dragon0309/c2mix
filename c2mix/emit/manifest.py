"""Write manifest.json (spec §7.5): what was decided, and how to map symbols back."""
from __future__ import annotations

import hashlib
import json
import platform
import subprocess
import sys
from pathlib import Path

from ..mixfmt.writer import to_str
from ..vc.assemble import VC


def _tool_versions(cfg) -> dict:
    out = {"python": sys.version.split()[0], "platform": platform.platform()}
    for tool in ("clang", "opt"):
        name = (cfg.data.get("toolchain") or {}).get(tool) if cfg else None
        if name:
            try:
                p = subprocess.run([name, "--version"], capture_output=True, text=True)
                out[tool] = p.stdout.strip().splitlines()[0] if p.stdout else "not available"
            except OSError:
                out[tool] = "not available"
    try:
        z3 = subprocess.run([cfg.data["solver"]["range"]["bin"], "--version"],
                            capture_output=True, text=True).stdout.strip()
        out["z3"] = z3
    except OSError:
        out["z3"] = "not available"
    b = cfg.path(cfg.data["solver"]["mix"]["bin"])
    if b.exists():
        out["mix_solver"] = {"path": str(b),
                             "sha256": hashlib.sha256(b.read_bytes()).hexdigest()[:16],
                             "mtime": b.stat().st_mtime}
    return out


def build(vcs: list[VC], target_name: str, opts, cfg=None, files=None,
          spec_source: str | None = None, frontend: dict | None = None) -> dict:
    files = files or {}
    cuts = []
    for vc in vcs:
        decisions: dict[str, int] = {}
        rules_used: dict[str, int] = {}
        for n in vc.seg.notes:
            decisions[str(n.get("decision"))] = decisions.get(str(n.get("decision")), 0) + 1
            rules_used[n["rule"]] = rules_used.get(n["rule"], 0) + 1
        cuts.append({
            "index": vc.index,
            "from": str(vc.point_from),
            "to": str(vc.point_to),
            "files": files.get(vc.index, {}),
            "counts": {"declarations": len(vc.seg.decls),
                       "range_statements": len(vc.seg.bv),
                       "algebraic_statements": len(vc.seg.alg),
                       "safety_obligations": len(vc.seg.safety),
                       "premises_range": len(vc.premise_range),
                       "premises_algebraic": len(vc.premise_alg),
                       "goals": len(vc.goal_alg)},
            "decisions": decisions,
            "rules": rules_used,
            "alg_free": sum(1 for n in vc.seg.notes if n.get("warning") == "W-ALG-FREE"),
            "hints": {"proved": [str(h) for h in vc.hints],
                      "emitted": [str(h) for h in vc.hints] if opts.hints == "emit" else []},
            "carried": [{"from": p, "fact": f} for p, f in vc.carried],
            "moduli": sorted({to_str(m) for t in vc.goal_alg
                              if isinstance(t, list) and t[0].startswith("eqmodP")
                              for m in t[3:]}),
            "trivial": vc.trivial,
        })
    return {
        "target": target_name,
        "command": " ".join(sys.argv),
        "options": vars(opts),
        "tools": _tool_versions(cfg) if cfg else {},
        "spec_sha256": _digest(spec_source),
        "ab_only": opts.int_encoding == "bv2int" or opts.ghost == "legacy-pow2",
        "frontend": frontend or {},
        "cuts": cuts,
        "symbols": _symbol_table(vcs, (frontend or {}).get("origins")),
    }


def _digest(spec_source: str | None) -> str | None:
    """The specification's contents, not the path it happens to sit at."""
    if not spec_source:
        return None
    p = Path(spec_source)
    data = p.read_bytes() if p.exists() else spec_source.encode()
    return hashlib.sha256(data).hexdigest()[:16]


def _symbol_table(vcs: list[VC], origins: dict | None = None) -> dict:
    """SMT name -> what it came from (§7.5): the registered object and index, or the
    LLVM value and source line the frontend produced it from."""
    origins = origins or {}
    out: dict[str, dict] = {}
    for vc in vcs:
        for name, sort in vc.seg.decls.items():
            entry = out.setdefault(name, {"sort": to_str(sort) if isinstance(sort, list) else sort,
                                          "cuts": []})
            entry["cuts"].append(vc.index)
            src = origins.get(name.removeprefix("s__"))
            if src and "origin" not in entry:
                entry["origin"] = src
    return dict(sorted(out.items()))


def write(manifest: dict, path: str | Path) -> Path:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(manifest, indent=1, sort_keys=False) + "\n", encoding="utf-8")
    return path
