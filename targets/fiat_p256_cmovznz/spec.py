"""fiat-crypto `fiat_p256_cmovznz_u64`: out1 = arg1 ? arg3 : arg2, written as a mask."""
from c2mix.spec.dsl import In, Out, Target, eq, rng


def build():
    t = Target("fiat_p256_cmovznz_u64",
               args={"out1": Out("uint64_t"), "arg1": In("fiat_p256_uint1"),
                     "arg2": In("uint64_t"), "arg3": In("uint64_t")})
    o1 = t.arg("out1").exit
    c, a2, a3 = (t.arg(n).entry for n in ("arg1", "arg2", "arg3"))
    cond = t.arg("arg1").entry
    t.pre(range=[rng(0 <= cond < 2)])
    t.post(alg=[eq(o1, a2 + c * (a3 - a2))])       # the L12 shape (§6.3)
    return t
