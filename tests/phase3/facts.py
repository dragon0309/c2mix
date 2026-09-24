"""A3.0 — the toolchain facts LF1–LF4, measured rather than assumed (spec §2.0).

Every one of these was "待實測" while the spec was written, and §9's phase 3 starts by
turning them into measurements. Each check returns (holds, evidence) so the acceptance
report can print what was actually observed.
"""
from __future__ import annotations

import re
import shutil
from pathlib import Path

from c2mix.frontend import llparse
from c2mix.frontend.toolchain import CFLAGS, Toolchain

POISON = re.compile(r"(?<![\w.])(nsw|nuw|exact|nneg|disjoint|samesign)(?![\w.])")

PROBE = """
#include <stdint.h>
static const int16_t table[8] = {2285, 2571, 2970, 1812, 1493, 1422, 287, 202};
int16_t probe(int16_t a, int16_t b, int i) {
  int16_t t = a;
  for (int k = 0; k < 4; k++) t = (int16_t)(t * 2 + b + table[k]);
  int32_t w = (int32_t)a * (int32_t)b;
  uint32_t u = (uint32_t)w >> 3;
  int32_t s = w >> 5;
  return (int16_t)(t + (int16_t)(u + s) + table[i & 7]);
}
"""

PROBE128 = """
#include <stdint.h>
void probe128(uint64_t *lo, uint64_t *hi, uint64_t a, uint64_t b) {
  unsigned __int128 p = (unsigned __int128)a * b;
  *lo = (uint64_t)p;
  *hi = (uint64_t)(p >> 64);
}
"""


def _compile(tc: Toolchain, work: Path, name: str, source: str, flags) -> Path:
    work.mkdir(parents=True, exist_ok=True)
    src = work / f"{name}.c"
    src.write_text(source)
    out = work / f"{name}.ll"
    tc.run([tc.clang, *flags, "-S", "-emit-llvm", str(src), "-o", str(out)])
    return out


def lf1(tc: Toolchain, work: Path) -> tuple[bool, str]:
    """clang -O0 marks functions `optnone`, and then mem2reg does nothing;
    -Xclang -disable-O0-optnone is what lets it run."""
    plain = [f for f in CFLAGS if f not in ("-Xclang", "-disable-O0-optnone")]
    a = _compile(tc, work, "lf1_plain", PROBE, plain)
    b = _compile(tc, work, "lf1_enabled", PROBE, CFLAGS)
    ra, rb = work / "lf1_plain.m2r.ll", work / "lf1_enabled.m2r.ll"
    tc.mem2reg(a, ra)
    tc.mem2reg(b, rb)
    left, right = ra.read_text().count("alloca"), rb.read_text().count("alloca")
    holds = "optnone" in a.read_text() and "optnone" not in b.read_text() \
        and left > 0 and right == 0
    return holds, (f"optnone present at -O0: {'optnone' in a.read_text()}; "
                   f"allocas after mem2reg: {left} without the flag, {right} with it")


def lf2(tc: Toolchain, work: Path, extra: list[Path] = ()) -> tuple[bool, str]:
    """-fwrapv keeps every poison-producing flag out of the IR."""
    nowrap = [f for f in CFLAGS if f != "-fwrapv"]
    a = _compile(tc, work, "lf2_nowrap", PROBE, nowrap)
    b = _compile(tc, work, "lf2_wrapv", PROBE, CFLAGS)
    ra, rb = work / "lf2_nowrap.m2r.ll", work / "lf2_wrapv.m2r.ll"
    tc.mem2reg(a, ra)
    tc.mem2reg(b, rb)
    without = len(POISON.findall(_instructions(ra.read_text())))
    with_flag = len(POISON.findall(_instructions(rb.read_text())))
    others = {}
    for ll in extra:
        others[ll.parent.parent.name] = len(POISON.findall(_instructions(ll.read_text())))
    holds = with_flag == 0 and without > 0 and not any(others.values())
    detail = f"poison flags: {without} without -fwrapv, {with_flag} with it"
    if others:
        detail += f"; every target's IR: {sum(others.values())} over {len(others)} target(s)"
    return holds, detail


def _instructions(text: str) -> str:
    return "\n".join(l for l in text.splitlines() if l.startswith("  "))


def lf3(tc: Toolchain, work: Path) -> tuple[bool, str]:
    """A `const` table is read with a GEP on a `constant` global plus a load, and the
    index is a constant once the loop is unrolled — so the executor can fold it."""
    ll = _compile(tc, work, "lf3", PROBE, CFLAGS)
    m2r = tc.mem2reg(ll, work / "lf3.m2r.ll")
    mod = llparse.parse(m2r.read_text(), str(m2r))
    g = next((x for x in mod.globals if "table" in x.name), None)
    fn = mod.function("probe")
    geps = [i for b in fn.blocks for i in b.instrs
            if i.op == "getelementptr" and str(i.args[0]).endswith(g.name.lstrip("@"))]
    loads = [i for b in fn.blocks for i in b.instrs if i.op == "load"]
    holds = g is not None and g.constant and len(geps) >= 1 and len(loads) >= 1
    return holds, (f"{g.name}: constant={g.constant}, {len(geps)} GEP(s) on it, "
                   f"{len(loads)} load(s) in the function")


def lf4(tc: Toolchain, work: Path, fiat: Path | None = None) -> tuple[bool, str]:
    """`unsigned __int128` becomes i128 arithmetic, and fiat-crypto's P-256 source
    stays inside the supported subset."""
    ll = _compile(tc, work, "lf4", PROBE128, CFLAGS)
    m2r = tc.mem2reg(ll, work / "lf4.m2r.ll")
    text = m2r.read_text()
    has_i128 = "i128" in text and "mul i128" in text
    detail = f"i128 arithmetic present: {has_i128}"
    holds = has_i128
    if fiat is not None:
        try:
            mod = llparse.parse(fiat.read_text(), str(fiat))
            ops = {i.op for f in mod.functions for b in f.blocks for i in b.instrs}
            i128 = fiat.read_text().count("i128")
            detail += f"; fiat P-256 IR parses, {i128} i128 mentions, opcodes {sorted(ops)}"
        except llparse.ParseError as e:
            holds = False
            detail += f"; fiat P-256 IR rejected: {e}"
    return holds, detail


def opcode_census(lls: dict) -> dict:
    """Which instructions the phase 3 and 4 targets actually use (A3.0)."""
    census: dict[str, int] = {}
    for ll in lls.values():
        mod = llparse.parse(Path(ll).read_text(), str(ll))
        for f in mod.functions:
            for b in f.blocks:
                for i in b.instrs:
                    census[i.op] = census.get(i.op, 0) + 1
    return dict(sorted(census.items(), key=lambda kv: -kv[1]))


def check_all(work: Path, target_lls: dict | None = None) -> list:
    """[(name, holds, evidence)] for LF1–LF4."""
    tc = Toolchain()
    missing = tc.missing()
    if missing:
        return [("toolchain", False, f"not installed: {', '.join(missing)}")]
    target_lls = target_lls or {}
    fiat = next((Path(v) for k, v in target_lls.items() if k.startswith("fiat")), None)
    return [
        ("LF1 -disable-O0-optnone lets mem2reg run", *lf1(tc, work)),
        ("LF2 -fwrapv leaves no poison flags", *lf2(tc, work, [Path(v) for v in target_lls.values()])),
        ("LF3 constant tables are GEP + load", *lf3(tc, work)),
        ("LF4 unsigned __int128 maps to i128", *lf4(tc, work, fiat)),
    ]
