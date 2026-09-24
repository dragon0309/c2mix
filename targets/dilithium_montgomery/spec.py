"""Dilithium `montgomery_reduce` (ref/reduce.c): r·2³² ≡ a (mod q), |r| < q.

The 64-bit input and R = 2³² are what make this different from Kyber's.
"""
from c2mix.spec.dsl import In, Out, Target, abs_lt, eqmod

from .params import MONT_BOUND, Q, R


def build():
    t = Target("montgomery_reduce",
               args={"a": In("int64_t"), "r": Out("int32_t")}, returns="r")
    a, r = t.arg("a").entry, t.arg("r").exit
    t.pre(range=[abs_lt(a, MONT_BOUND)])
    t.post(range=[abs_lt(r, Q)], alg=[eqmod(r * R, a, [Q])])
    return t
