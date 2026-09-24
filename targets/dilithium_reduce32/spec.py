"""Dilithium `reduce32` (ref/reduce.c): r ≡ a (mod q) with |r| ≤ 6283008."""
from c2mix.spec.dsl import In, Out, Target, eqmod, rng

from .params import Q, RED32_HI, RED32_OUT


def build():
    t = Target("reduce32",
               args={"a": In("int32_t"), "r": Out("int32_t")}, returns="r")
    a, r = t.arg("a").entry, t.arg("r").exit
    t.pre(range=[rng(-RED32_HI <= a < RED32_HI + 1)])
    t.post(range=[rng(-RED32_OUT <= r < RED32_OUT + 1)], alg=[eqmod(r, a, [Q])])
    return t
