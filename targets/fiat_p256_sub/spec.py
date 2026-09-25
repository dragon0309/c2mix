"""fiat-crypto `fiat_p256_sub`: out ≡ a − b (mod p), 0 ≤ out < p.

Subtraction commutes with the Montgomery map, so fiat's from_montgomery form and this
one say the same thing.
"""
from c2mix.spec.dsl import Array, In, Out, Target, eqmod, limbs, rng

from .params import LIMBS, P, W


def build():
    t = Target("fiat_p256_sub", args={"out1": Out(Array("uint64_t", LIMBS)),
                                      "arg1": In(Array("uint64_t", LIMBS)),
                                      "arg2": In(Array("uint64_t", LIMBS))})
    A, B, O = (limbs(list(t.arg(n)), W) for n in ("arg1", "arg2", "out1"))
    t.pre(range=[rng(0 <= A.entry < P), rng(0 <= B.entry < P)])
    t.post(range=[rng(0 <= O.exit < P)], alg=[eqmod(O.exit, A.entry - B.entry, [P])])
    return t
