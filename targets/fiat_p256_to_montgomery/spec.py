"""fiat-crypto `fiat_p256_to_montgomery`: out ≡ a·R (mod p), 0 ≤ out < p.

fiat states eval (from_montgomery out1) mod m = eval arg1 mod m, i.e. out·R⁻¹ ≡ a.
"""
from c2mix.spec.dsl import Array, In, Out, Target, eqmod, limbs, rng

from .params import LIMBS, P, R, W


def build():
    t = Target("fiat_p256_to_montgomery", args={"out1": Out(Array("uint64_t", LIMBS)),
                                                "arg1": In(Array("uint64_t", LIMBS))})
    A, O = (limbs(list(t.arg(n)), W) for n in ("arg1", "out1"))
    t.pre(range=[rng(0 <= A.entry < P)])
    t.post(range=[rng(0 <= O.exit < P)], alg=[eqmod(O.exit, A.entry * R, [P])])
    return t
