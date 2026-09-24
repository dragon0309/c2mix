"""A3.9: a conditional move written with a branch and with `?:` (spec §9, 第 3 階段).

Both selections are the L12 shape, so the specification is the same equation twice —
what is being tested is that the executor merges the two arms into `ite` and that the
result means what the C program means (G2, G3).
"""
from c2mix.spec.dsl import In, Out, Target, eq, rng


def build():
    t = Target("cmov_branch",
               args={"out1": Out("uint64_t"), "out2": Out("uint64_t"),
                     "c": In("uint8_t"), "a": In("uint64_t"), "b": In("uint64_t")})
    o1, o2 = t.arg("out1").exit, t.arg("out2").exit
    c, a, b = (t.arg(n).entry for n in ("c", "a", "b"))
    cond = t.arg("c").entry
    t.pre(range=[rng(0 <= cond < 2)])
    t.post(alg=[eq(o1, b + c * (a - b)), eq(o2, a + c * (b - a))])
    return t
