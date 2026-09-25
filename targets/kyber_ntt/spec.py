"""Kyber `ntt` (ref/ntt.c): seven Cooley–Tukey layers.

After layer k every block of length 256/2ᵏ is the input reduced modulo q and
x^deg − ζ, and every coefficient is below (k+1)·q in absolute value: each layer adds
fqmul's output, which is below q (montgomery_reduce's bound).

Two cut placements (target.toml [variants]):
  default  one cut after each layer (cuts.patch);
  half     one cut after layer 1 and after each half of layers 2–7 (cuts.half.patch),
           the granularity of the golden pqclean_kyber768_avx2_noAssume. Between the
           two halves of layer k, coefficients 0–127 are at layer k and 128–255 are
           still at layer k − 1.
"""
from c2mix.lib import ntt
from c2mix.spec.dsl import Array, Indet, InOut, Target, abs_lt, eqmod, poly

from .params import LAYERS, N, Q, R, ZETAS


def build(variant=None):
    t = Target("ntt", args={"r": InOut(Array("int16_t", N))})
    r, x = t.arg("r"), Indet("x")
    inp = t.ghost("inp", poly([r[i].entry for i in range(N)], x))
    t.pre(range=[abs_lt(r[i].entry, Q) for i in range(N)])
    layers = ntt.ct_schedule(N, Q, ZETAS[1:], R=R, layers=LAYERS)

    def state(c, done):
        """done[h] = the layer the half h (coefficients 128h … 128h+127) has reached."""
        for h in (0, 1):
            lo, hi = h * N // 2, (h + 1) * N // 2
            c.range(abs_lt(r[i].at(c), (done[h] + 1) * Q) for i in range(lo, hi))
            c.alg(eqmod(inp, poly([r[j].at(c) for j in range(b.lo, b.hi)], x),
                        [Q, x ** b.deg - b.zeta])
                  for b in layers[done[h] - 1] if lo <= b.lo and b.hi <= hi)

    c, k = None, 0
    if variant is None:
        for layer in range(1, LAYERS + 1):
            k += 1
            c = t.cut("1", k)
            state(c, (layer, layer))
    elif variant == "half":
        k += 1
        c = t.cut("1", k)
        c.range(abs_lt(r[i].at(c), 2 * Q) for i in range(N))
        c.alg(eqmod(inp, poly([r[j].at(c) for j in range(b.lo, b.hi)], x),
                    [Q, x ** b.deg - b.zeta]) for b in layers[0])
        for layer in range(2, LAYERS + 1):
            for done in ((layer, layer - 1), (layer, layer)):
                k += 1
                c = t.cut("1", k)
                state(c, done)
    else:
        raise ValueError(f"unknown variant {variant!r}")
    t.post(same_as=c)
    return t
