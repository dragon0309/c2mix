#!/usr/bin/env python3
"""Property testing for the rule instances z3 cannot prove in reasonable time.

A 64- or 128-bit multiply lemma needs 128/256-bit non-linear reasoning; z3 does not
finish either the mixed encoding or its QF_BV image. Spec A1.1 already foresees this
for 128-bit and asks for 10^6 random samples instead; measurement showed the same is
needed at 64-bit. This checks the statements the lowering actually emits (the same
evaluator A1.3 uses), so it tests the emitted rule, not a re-derivation of it.

usage: tests/phase1/property.py [--samples 1000000] [--width 64,128]
"""
from __future__ import annotations

import argparse
import random
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from c2mix.ir import intervals as iv        # noqa: E402
from c2mix.ir import interp                 # noqa: E402
from c2mix.ir.ops import Builder            # noqa: E402
from c2mix.lower import evaluate, rules     # noqa: E402


def mul_program(width: int, signed: bool):
    b = Builder()
    a = b.input("a", width, signed)
    c = b.input("b", width, signed)
    b.mul(a, c)
    return b.build()


def edge_values(width: int, signed: bool) -> list[int]:
    lo = -(1 << (width - 1)) if signed else 0
    hi = (1 << (width - 1)) - 1 if signed else (1 << width) - 1
    vals = {lo, hi, 0, 1, -1 if signed else hi - 1, lo + 1, hi - 1,
            1 << (width // 2), (1 << (width // 2)) - 1}
    return sorted(v for v in vals if lo <= v <= hi)


def check_mul(width: int, signed: bool, samples: int, seed: int = 0) -> tuple[int, list[str]]:
    """Returns (checked, failures). Edge values first, then random pairs."""
    prog = mul_program(width, signed)
    seg = rules.lower(prog, iv.analyze(prog))
    widths = evaluate.widths_of(seg)
    rng = random.Random(seed)
    edges = edge_values(width, signed)
    lo = -(1 << (width - 1)) if signed else 0
    hi = (1 << (width - 1)) - 1 if signed else (1 << width) - 1
    pairs = [(x, y) for x in edges for y in edges]
    n = 0
    for i in range(samples):
        a, b = pairs[i] if i < len(pairs) else (rng.randint(lo, hi), rng.randint(lo, hi))
        patterns = interp.run(prog, {"a": a, "b": b})
        env = evaluate.Env({k: v for k, v in patterns.items() if k in widths}, widths)
        evaluate.solve_definitions(seg, env)
        bad = evaluate.check_segment(seg, env)
        n += 1
        if bad:
            return n, [f"a={a} b={b}: {m}" for m in bad]
    return n, []


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples", type=int, default=1_000_000)
    ap.add_argument("--widths", default="64,128")
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    status = 0
    for width in (int(w) for w in args.widths.split(",")):
        for signed in (True, False):
            t0 = time.monotonic()
            n, bad = check_mul(width, signed, args.samples, args.seed)
            dt = time.monotonic() - t0
            tag = f"L4' mul w={width} {'signed' if signed else 'unsigned'}"
            print(f"{tag}: {n} samples in {dt:.0f}s -> {'OK' if not bad else 'FAILED'}")
            for m in bad[:5]:
                print("   ", m)
            status |= 1 if bad else 0
    return status


if __name__ == "__main__":
    sys.exit(main())
