"""T2a: an 8-point NTT, q = 17, three layers (spec §9, phase 2).

Small but structurally the real thing: Montgomery butterflies over int16, a cut after
each layer, and per-block congruences with two moduli (q and x^deg − ζ). The
factorisation is complete, so the leaves are linear.

q, the zeta table and R live here, never in the core (G10).
"""
from c2mix.ir.trace import TraceBuilder
from c2mix.lib import ntt
from c2mix.lib.mont import Montgomery
from c2mix.spec.dsl import Array, Indet, InOut, Target, abs_lt, eqmod, poly

N = 8
Q = 17
MONT = Montgomery(Q, 16)
QINV = MONT.signed_q_inv()
ROOT = 3                      # a primitive 2N-th root of unity mod 17


def _bitrev(i: int, bits: int) -> int:
    return int(format(i, f"0{bits}b")[::-1], 2)


# zetas in the order the program uses them, in Montgomery form, as the reference
# implementations tabulate them
ZETAS = [MONT.to_montgomery(pow(ROOT, _bitrev(i, 3), Q)) for i in range(N)]


def fqmul(b, a, zeta_const, q_const, qinv_const):
    """Montgomery multiply: (a·zeta)·R⁻¹ mod q, exactly as ref/reduce.c computes it."""
    p32 = b.mul(b.sext(zeta_const, 32), b.sext(a, 32))
    lo = b.extract(p32, 15, 0, signed=True)
    u = b.mul(b.sext(lo, 32), qinv_const)
    t = b.extract(u, 15, 0, signed=True)
    m = b.mul(b.sext(t, 32), q_const)
    d = b.sub(p32, m)
    r32 = b.ashr(d, 16)
    return b.extract(r32, 15, 0, signed=True)


def build_trace():
    tb = TraceBuilder()
    r = tb.input("r", 16, True, count=N)
    tb.entry()
    b = tb.b
    qinv32 = b.const(QINV, 32, True)
    q32 = b.const(Q, 32, True)
    zetas16 = {k: b.const(ZETAS[k], 16, True) for k in range(1, N)}  # zetas[0] is unused

    cur = list(r)
    k = 1
    half = N // 2
    layer = 0
    while half >= 1:
        for start in range(0, N, 2 * half):
            zeta = zetas16[k]
            k += 1
            for j in range(start, start + half):
                t = fqmul(b, cur[j + half], zeta, q32, qinv32)
                cur[j + half] = b.sub(cur[j], t)
                cur[j] = b.add(cur[j], t)
        layer += 1
        for i, v in enumerate(cur):
            tb.store("r", i, v)
        tb.cut("layer", layer)
        half //= 2
    return tb.done()


def schedule():
    return ntt.ct_schedule(N, Q, ZETAS[1:], R=MONT.R, layers=3)


def build_spec():
    t = Target("ntt8", args={"r": InOut(Array("int16_t", N))})
    r, x = t.arg("r"), Indet("x")
    inp = t.ghost("inp", poly([r[i].entry for i in range(N)], x))
    t.pre(range=[abs_lt(r[i].entry, Q) for i in range(N)])
    c = None
    for k, blocks in enumerate(schedule(), 1):
        c = t.cut("layer", k)
        c.range(abs_lt(r[i].at(c), (k + 1) * Q) for i in range(N))
        c.alg(eqmod(inp, poly([r[j].at(c) for j in range(bl.lo, bl.hi)], x),
                    [Q, x ** bl.deg - bl.zeta]) for bl in blocks)
    t.post(same_as=c)
    return t


def build():
    return build_trace(), build_spec()
