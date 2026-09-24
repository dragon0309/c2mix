"""fiat-crypto `fiat_p256_mulx_u64`: out1 + 2⁶⁴·out2 = arg1·arg2."""
from c2mix.spec.dsl import In, Out, Target, eq

from .params import RADIX


def build():
    t = Target("fiat_p256_mulx_u64",
               args={"out1": Out("uint64_t"), "out2": Out("uint64_t"),
                     "arg1": In("uint64_t"), "arg2": In("uint64_t")})
    o1, o2 = t.arg("out1").exit, t.arg("out2").exit
    a1, a2 = t.arg("arg1").entry, t.arg("arg2").entry
    t.post(alg=[eq(o1 + o2 * RADIX, a1 * a2)])
    return t
