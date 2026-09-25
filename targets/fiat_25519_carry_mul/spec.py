"""fiat-crypto `fiat_25519_carry_mul`: out ≡ a·b (mod 2²⁵⁵ − 19), radix 2⁵¹.

fiat states the bounds on the types rather than on the function: arguments are
`loose_field_element`s, every limb in [0, 0x18000000000000], and the result is a
`tight_field_element`, every limb in [0, 0x8000000000000] (both inclusive).
"""
from c2mix.spec.dsl import Array, In, Out, Target, eqmod, limbs, rng

from .params import LIMBS, LOOSE, P, RADIX_BITS, TIGHT


def build():
    t = Target("fiat_25519_carry_mul", args={"out1": Out(Array("uint64_t", LIMBS)),
                                             "arg1": In(Array("uint64_t", LIMBS)),
                                             "arg2": In(Array("uint64_t", LIMBS))})
    a, b, o = t.arg("arg1"), t.arg("arg2"), t.arg("out1")
    A, B, O = (limbs(list(v), RADIX_BITS) for v in (a, b, o))
    t.pre(range=[rng(0 <= v.entry < LOOSE + 1) for v in list(a) + list(b)])
    t.post(range=[rng(0 <= v.exit < TIGHT + 1) for v in o],
           alg=[eqmod(O.exit, A.entry * B.entry, [P])])
    return t
