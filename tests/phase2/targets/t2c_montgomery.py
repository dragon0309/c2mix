"""T2c: scalar Montgomery reduction (spec §9, phase 2) — the H1 hint target.

The same program as extend_z3/working/cbmc_small/02_montgomery.c:

    t = (int16_t)a * QINV;
    t = (a - (int32_t)t * Q) >> 16;

with the post-condition t·2¹⁶ ≡ a (mod Q). The proof needs a fact the algebraic layer
cannot see on its own: the low 16 bits of a − t·Q are zero, which is exactly the H1
candidate the low witness of L7 offers.

Q and QINV live here, in the target, never in the core (G10).
"""
from c2mix.ir.trace import TraceBuilder
from c2mix.lib.mont import Montgomery
from c2mix.spec.dsl import In, Out, Target, abs_lt, eqmod

Q = 3329
MONT = Montgomery(Q, 16)
QINV = MONT.signed_q_inv()          # −q⁻¹ mod 2¹⁶ as an int16, i.e. −3327
BOUND = Q * (1 << 15)               # |a| < q·2¹⁵


def build_trace():
    tb = TraceBuilder()
    (a,) = tb.input("a", 32, True)
    tb.entry()
    b = tb.b
    a16 = b.extract(a, 15, 0, signed=True)          # (int16_t)a
    a16w = b.sext(a16, 32)
    qinv = b.const(QINV, 32, True)
    u = b.mul(a16w, qinv)                           # int arithmetic at 32 bits
    t = b.extract(u, 15, 0, signed=True)            # (int16_t)(...)
    tw = b.sext(t, 32)
    qc = b.const(Q, 32, True)
    m = b.mul(tw, qc)
    d = b.sub(a, m)
    r32 = b.ashr(d, 16)                             # L7: the low witness is the hint
    r = b.extract(r32, 15, 0, signed=True)          # value-preserving cast
    tb.register("r", [r])
    return tb.done()


def build_spec():
    t = Target("montgomery_reduce", args={"a": In("int32_t"), "r": Out("int16_t")})
    a, r = t.arg("a"), t.arg("r")
    t.pre(range=[abs_lt(a.entry, BOUND)])
    t.post(range=[abs_lt(r.exit, Q)],
           alg=[eqmod(r.exit * (1 << 16), a.entry, [Q])])
    return t


def build():
    return build_trace(), build_spec()
