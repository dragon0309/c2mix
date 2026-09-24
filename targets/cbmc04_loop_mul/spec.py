"""cbmc_small 04: shift-and-add multiply — a small loop with an input-dependent `if`."""
from c2mix.spec.dsl import In, Out, Target, eqmod, rng


def build():
    t = Target("loop_mul",
               args={"acc": Out("uint16_t"), "x": In("uint16_t"), "k": In("uint16_t")})
    acc, x, k = t.arg("acc").exit, t.arg("x").entry, t.arg("k").entry
    kk = t.arg("k").entry
    t.pre(range=[rng(0 <= kk < 16)])
    t.post(range=[rng(0 <= acc < 1 << 16)], alg=[eqmod(acc, x * k, [1 << 16])])
    return t
