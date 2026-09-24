"""cbmc_small 01: 8-bit addition commutes (spec §9.0, phase 3)."""
from c2mix.spec.dsl import In, Out, Target, eq, rng


def build():
    t = Target("add_comm",
               args={"s": Out("uint8_t"), "t": Out("uint8_t"),
                     "x": In("uint8_t"), "y": In("uint8_t")})
    s, u = t.arg("s").exit, t.arg("t").exit
    t.post(range=[rng(0 <= s < 256)], alg=[eq(s, u)])
    return t
