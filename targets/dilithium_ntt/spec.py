"""Dilithium `ntt` (ref/ntt.c): eight Cooley–Tukey layers, one cut after each.

The factorisation is complete, so after the last layer every coefficient is the input
evaluated at one root: r[j] ≡ inp (mod q, x − ζ).

The bounds are derived from montgomery_reduce's output bound (§9 phase 4): it returns
|t| < q for inputs below q·2³¹, so a layer that starts below k·q ends below (k+1)·q.
Its input here is ζ·a with |ζ| ≤ (q−1)/2 and |a| < 8q, far inside q·2³¹; that is
what the range VCs check (the EXACT safety obligations on the 64-bit product).
The pre-condition |a| < q covers every caller in ref/sign.c: y and z below γ₁, s₁ and
s₂ below η, the challenge in {−1, 0, 1}, and t₁·2¹³ ≤ q − 1.
"""
from c2mix.lib import ntt
from c2mix.spec.dsl import Array, Indet, InOut, Target, abs_lt, eqmod, poly

from .params import LAYERS, N, Q, R, ZETAS


def build():
    t = Target("ntt", args={"a": InOut(Array("int32_t", N))})
    a, x = t.arg("a"), Indet("x")
    inp = t.ghost("inp", poly([a[i].entry for i in range(N)], x))
    t.pre(range=[abs_lt(a[i].entry, Q) for i in range(N)])
    c = None
    for k, blocks in enumerate(ntt.ct_schedule(N, Q, ZETAS[1:], R=R, layers=LAYERS), 1):
        c = t.cut("1", k)
        c.range(abs_lt(a[i].at(c), (k + 1) * Q) for i in range(N))
        c.alg(eqmod(inp, poly([a[j].at(c) for j in range(b.lo, b.hi)], x),
                    [Q, x ** b.deg - b.zeta]) for b in blocks)
    t.post(same_as=c)
    return t
