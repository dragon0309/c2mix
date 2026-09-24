#!/usr/bin/env python3
"""Random IR programs for A1.3 (statements true on real runs) and A1.4 (intervals).

Generates straight-line programs over mixed widths and signednesses, runs them on
random inputs drawn from the precondition, and checks that
  * every statement the lowering emitted is true on that run (A1.3), and
  * every concrete value lies in its analyzed interval (A1.4).

usage: tests/phase1/fuzz.py [--programs 1000] [--inputs 100] [--seed 0]
"""
from __future__ import annotations

import argparse
import random
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from c2mix.ir import intervals as iv          # noqa: E402
from c2mix.ir import interp                   # noqa: E402
from c2mix.ir.ops import Builder, Value       # noqa: E402
from c2mix.lower import evaluate, rules       # noqa: E402

WIDTHS = (4, 8, 16, 32, 64)


@dataclass
class Case:
    prog: object
    pre: dict


def random_program(rng: random.Random, length: int) -> Case:
    b = Builder()
    pool: list[Value] = []
    pre: dict = {}
    for i in range(rng.randint(2, 5)):
        w = rng.choice(WIDTHS)
        signed = rng.random() < 0.5
        v = b.input(f"in{i}", w, signed)
        pool.append(v)
        lo, hi = v.lo, v.hi
        if rng.random() < 0.5:                 # a narrower precondition makes EXACT reachable
            span = max(1, (hi - lo) // rng.choice((4, 16, 256)))
            start = rng.randint(lo, hi - span)
            lo, hi = start, start + span
        pre[v.name] = iv.Interval(lo, hi)
    pool.append(b.input("c0", 1, False))

    def pick(width=None, signed=None, exclude_one=False):
        cands = [v for v in pool
                 if (width is None or v.width == width)
                 and (signed is None or v.signed == signed)
                 and not (exclude_one and v.width == 1)]
        return rng.choice(cands) if cands else None

    ops = ["add", "sub", "neg", "mul", "and", "or", "xor", "not", "shl", "shr",
           "sext", "zext", "extract", "cmp", "ite", "const", "mask"]
    for _ in range(length):
        op = rng.choice(ops)
        try:
            v = _emit(b, rng, op, pick)
        except (ValueError, IndexError):
            v = None
        if v is not None:
            pool.append(v)
    return Case(b.build(), pre)


def _emit(b: Builder, rng: random.Random, op: str, pick):
    if op == "const":
        w = rng.choice(WIDTHS)
        signed = rng.random() < 0.5
        lo = -(1 << (w - 1)) if signed else 0
        hi = (1 << (w - 1)) - 1 if signed else (1 << w) - 1
        return b.const(rng.randint(lo, hi), w, signed)
    if op in ("add", "sub", "mul", "and", "or", "xor"):
        a = pick(exclude_one=True)
        if a is None:
            return None
        bb = pick(width=a.width, signed=a.signed)
        return b.binop(op, a, bb) if bb is not None else None
    if op in ("neg", "not"):
        a = pick(exclude_one=True)
        return (b.neg(a) if op == "neg" else b.not_(a)) if a else None
    if op == "shl":
        a = pick(exclude_one=True)
        return b.shl(a, rng.randrange(a.width)) if a else None
    if op == "shr":
        a = pick(exclude_one=True)
        if a is None:
            return None
        k = rng.randrange(a.width)
        return b.ashr(a, k) if a.signed else b.lshr(a, k)
    if op in ("sext", "zext"):
        signed = op == "sext"
        a = pick(signed=signed, exclude_one=True)
        if a is None or a.width >= 64:
            return None
        target = rng.choice([w for w in WIDTHS if w > a.width])
        return b.sext(a, target) if signed else b.zext(a, target)
    if op == "extract":
        a = pick(exclude_one=True)
        if a is None:
            return None
        hi = rng.randrange(a.width)
        lo = rng.randint(0, hi)
        return b.extract(a, hi, lo, signed=rng.random() < 0.5 and hi - lo > 0)
    if op == "cmp":
        a = pick(exclude_one=True)
        if a is None:
            return None
        bb = pick(width=a.width, signed=a.signed)
        if bb is None:
            return None
        preds = ("eq", "ne", "slt", "sle") if a.signed else ("eq", "ne", "ult", "ule")
        return b.cmp(rng.choice(preds), a, bb)
    if op == "ite":
        c = pick(width=1)
        a = pick(exclude_one=True)
        if c is None or a is None:
            return None
        bb = pick(width=a.width, signed=a.signed)
        return b.ite(c, a, bb) if bb is not None else None
    if op == "mask":
        a = pick(exclude_one=True)
        if a is None:
            return None
        k = rng.randint(1, a.width - 1)
        m = b.const(((1 << k) - 1) if not a.signed else
                    interp.interpret((1 << k) - 1, a.width, True), a.width, a.signed)
        return b.and_(a, m)
    return None


def run_case(case: Case, rng: random.Random, n_inputs: int, mode: str = "alias"):
    """Returns a list of failures ('' when the case is clean)."""
    prog = case.prog
    an = iv.analyze(prog, case.pre)
    seg = rules.lower(prog, an, mode=mode)
    widths = evaluate.widths_of(seg)
    failures = []
    for _ in range(n_inputs):
        inputs = {v.name: rng.randint(case.pre[v.name].lo, case.pre[v.name].hi)
                  if v.name in case.pre else rng.randint(v.lo, v.hi) for v in prog.inputs}
        env_patterns = interp.run(prog, inputs)
        failures += [f"A1.4 {m}" for m in iv.check_containment(prog, an, env_patterns)]
        env = evaluate.Env({k: v for k, v in env_patterns.items() if k in widths}, widths)
        evaluate.solve_definitions(seg, env)
        failures += [f"A1.3 {m}" for m in evaluate.check_segment(seg, env)]
        if failures:
            failures.append(f"inputs: {inputs}")
            break
    return failures


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--programs", type=int, default=1000)
    ap.add_argument("--inputs", type=int, default=100)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--min-length", type=int, default=20)
    ap.add_argument("--max-length", type=int, default=200)
    args = ap.parse_args()

    rng = random.Random(args.seed)
    bad = 0
    stats = {}
    for i in range(args.programs):
        case = random_program(rng, rng.randint(args.min_length, args.max_length))
        for n in case.prog.instrs:
            stats[n.op] = stats.get(n.op, 0) + 1
        failures = run_case(case, rng, args.inputs)
        if failures:
            bad += 1
            print(f"program {i} (seed {args.seed}):")
            for f in failures[:6]:
                print("   ", f)
            if bad > 3:
                break
    print(f"{args.programs} programs x {args.inputs} inputs: "
          f"{'OK' if not bad else str(bad) + ' FAILED'}")
    print("ops covered:", dict(sorted(stats.items())))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
