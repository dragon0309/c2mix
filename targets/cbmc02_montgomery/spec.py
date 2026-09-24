"""cbmc_small 02: scalar Montgomery reduction — the H1 hint target (spec §6.4)."""
from c2mix.spec.dsl import In, Out, Target, abs_lt, eqmod

from .params import BOUND, Q, R


def build():
    t = Target("montgomery_reduce",
               args={"a": In("int32_t"), "r": Out("int16_t")}, returns="r")
    a, r = t.arg("a").entry, t.arg("r").exit
    t.pre(range=[abs_lt(a, BOUND)])
    t.post(range=[abs_lt(r, Q)], alg=[eqmod(r * R, a, [Q])])
    return t
