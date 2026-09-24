"""T2b: 2-limb modular addition, radix 2³², p = 2⁶¹ − 1 (spec §9, phase 2).

    S = A + B                    limb-wise, the carry is the high half of a 64-bit add
    D = S − p                    wraps when S < p, so the top bit is the borrow
    O = borrow ? S : D           conditional subtraction, the L12 select

Exercises the limb interpretation, a carry that is a real value rather than a witness,
and L12. p and the radix live here, not in the core (G10).
"""
from c2mix.ir.trace import TraceBuilder
from c2mix.spec.dsl import Array, In, Out, Target, eqmod, limbs, rng

RADIX = 32
P = (1 << 61) - 1
LIMB_HI = 1 << 29                 # A < p forces the top limb below 2²⁹


def build_trace():
    tb = TraceBuilder()
    a = tb.input("a", 32, False, count=2)
    b_in = tb.input("b", 32, False, count=2)
    tb.entry()
    b = tb.b

    # S = A + B, limb by limb; the carry out of limb 0 is the high half of the 64-bit sum
    s0w = b.add(b.zext(a[0], 64), b.zext(b_in[0], 64))
    s0 = b.extract(s0w, 31, 0)
    carry = b.extract(s0w, 63, 32)
    s1w = b.add(b.add(b.zext(a[1], 64), b.zext(b_in[1], 64)), b.zext(carry, 64))
    s1 = b.extract(s1w, 31, 0)

    # S as one 64-bit value, then the conditional subtraction
    sw = b.add(b.shl(b.zext(s1, 64), 32), b.zext(s0, 64))
    p64 = b.const(P, 64, False)
    d = b.sub(sw, p64)                       # wraps when S < p
    borrow = b.lshr(d, 63)                   # 1 exactly when it wrapped
    cond = b.extract(borrow, 0, 0)
    out = b.ite(cond, sw, d)                 # L12: keep S when the subtraction borrowed

    o0 = b.extract(out, 31, 0)
    o1 = b.extract(out, 63, 32)
    tb.register("o", [o0, o1])
    return tb.done()


def build_spec():
    t = Target("limb_add", args={"a": In(Array("uint32_t", 2)),
                                 "b": In(Array("uint32_t", 2)),
                                 "o": Out(Array("uint32_t", 2))})
    A = limbs([t.arg("a")[i] for i in range(2)], RADIX)
    B = limbs([t.arg("b")[i] for i in range(2)], RADIX)
    O = limbs([t.arg("o")[i] for i in range(2)], RADIX)
    t.pre(range=[rng(0 <= A.entry < P), rng(0 <= B.entry < P),
                 rng(0 <= t.arg("a")[1].entry < LIMB_HI),
                 rng(0 <= t.arg("b")[1].entry < LIMB_HI)])
    t.post(range=[rng(0 <= O.exit < P)],
           alg=[eqmod(O.exit, A.entry + B.entry, [P])])
    return t


def build():
    return build_trace(), build_spec()
