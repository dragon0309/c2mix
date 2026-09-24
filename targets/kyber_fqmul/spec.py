"""Kyber `fqmul` (static in ref/ntt.c): r·2¹⁶ ≡ a·b (mod q)."""
from c2mix.spec.dsl import In, Out, Target, abs_lt, eqmod

from .params import Q, R


def build():
    t = Target("fqmul",
               args={"a": In("int16_t"), "b": In("int16_t"), "r": Out("int16_t")},
               returns="r")
    a, b, r = t.arg("a").entry, t.arg("b").entry, t.arg("r").exit
    t.pre(range=[abs_lt(a, Q), abs_lt(b, Q)])      # |a·b| < q·2¹⁵, montgomery_reduce's bound
    t.post(range=[abs_lt(r, Q)], alg=[eqmod(r * R, a * b, [Q])])
    return t
