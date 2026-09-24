"""cbmc_small 03: Barrett reduction to the centered representative."""
from c2mix.spec.dsl import In, Out, Target, eqmod, rng

from .params import HALF, Q


def build():
    t = Target("barrett_reduce",
               args={"a": In("int16_t"), "r": Out("int16_t")}, returns="r")
    a, r = t.arg("a").entry, t.arg("r").exit
    t.post(range=[rng(-HALF <= r < HALF + 1)], alg=[eqmod(r, a, [Q])])
    return t
