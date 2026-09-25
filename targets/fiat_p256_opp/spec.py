"""fiat-crypto `fiat_p256_opp`: out ≡ −a (mod p), 0 ≤ out < p."""
from c2mix.spec.dsl import Array, In, Out, Target, eqmod, limbs, rng

from .params import LIMBS, P, W


def build():
    t = Target("fiat_p256_opp", args={"out1": Out(Array("uint64_t", LIMBS)),
                                      "arg1": In(Array("uint64_t", LIMBS))})
    A, O = (limbs(list(t.arg(n)), W) for n in ("arg1", "out1"))
    t.pre(range=[rng(0 <= A.entry < P)])
    t.post(range=[rng(0 <= O.exit < P)], alg=[eqmod(O.exit, 0 - A.entry, [P])])
    return t
