"""fiat-crypto `fiat_p256_addcarryx_u64`: out1 + 2⁶⁴·out2 = arg1 + arg2 + arg3."""
from c2mix.spec.dsl import In, Out, Target, eq, rng

from .params import RADIX


def build():
    t = Target("fiat_p256_addcarryx_u64",
               args={"out1": Out("uint64_t"), "out2": Out("fiat_p256_uint1"),
                     "arg1": In("fiat_p256_uint1"), "arg2": In("uint64_t"),
                     "arg3": In("uint64_t")})
    o1, o2 = t.arg("out1").exit, t.arg("out2").exit
    a1, a2, a3 = (t.arg(n).entry for n in ("arg1", "arg2", "arg3"))
    carry_in = t.arg("arg1").entry
    carry_out = t.arg("out2").exit
    t.pre(range=[rng(0 <= carry_in < 2)])
    t.post(range=[rng(0 <= carry_out < 2)], alg=[eq(o1 + o2 * RADIX, a1 + a2 + a3)])
    return t
