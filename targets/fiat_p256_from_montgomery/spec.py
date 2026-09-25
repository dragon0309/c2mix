"""fiat-crypto `fiat_p256_from_montgomery`: out·R ≡ a (mod p), 0 ≤ out < p.

fiat states eval out1 mod m = eval arg1 · ((2⁶⁴)⁻¹ mod m)⁴ mod m; multiplying through
by R = (2⁶⁴)⁴ gives the form here, which needs no inverse.
"""
from c2mix.spec.dsl import Array, In, Out, Target, eqmod, limbs, rng

from .params import LIMBS, P, R, W


def build():
    t = Target("fiat_p256_from_montgomery", args={"out1": Out(Array("uint64_t", LIMBS)),
                                                  "arg1": In(Array("uint64_t", LIMBS))})
    A, O = (limbs(list(t.arg(n)), W) for n in ("arg1", "out1"))
    t.pre(range=[rng(0 <= A.entry < P)])
    t.post(range=[rng(0 <= O.exit < P)], alg=[eqmod(O.exit * R, A.entry, [P])])
    return t
