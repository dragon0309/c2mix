"""fiat-crypto `fiat_p256_mul`: Montgomery multiplication, out·R ≡ a·b (mod p).

fiat states it as eval (from_montgomery out1) = eval (from_montgomery arg1) ·
eval (from_montgomery arg2) mod m; multiplying through by R = 2²⁵⁶ gives the form here.
"""
from c2mix.spec.dsl import Array, In, Out, Target, eqmod, limbs, rng

from .params import LIMBS, P, R, W


def build():
    t = Target("fiat_p256_mul", args={"out1": Out(Array("uint64_t", LIMBS)),
                                      "arg1": In(Array("uint64_t", LIMBS)),
                                      "arg2": In(Array("uint64_t", LIMBS))})
    A, B, O = (limbs(list(t.arg(n)), W) for n in ("arg1", "arg2", "out1"))
    t.pre(range=[rng(0 <= A.entry < P), rng(0 <= B.entry < P)])
    t.post(range=[rng(0 <= O.exit < P)], alg=[eqmod(O.exit * R, A.entry * B.entry, [P])])
    return t
