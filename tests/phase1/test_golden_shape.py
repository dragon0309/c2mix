"""A1.5: a hand-written butterfly lane must lower to the shapes the golden uses.

The lane is written the way the AVX2 code multiplies: a same-width 16-bit multiply
whose product does not fit, so L4′ splits it into the low half (the program value,
golden's mulL) and the high half (a witness, golden's mulH). Reading that low half
as signed afterwards is what produces the L10 bridge (golden's tmp symbol).

Compared modulo symbol names ("shape"), with --int-encoding=bv2int so the reading
matches the golden's. The golden's high half is also a program value, because the
AVX2 code gets it from vpmulhw; mapping that intrinsic onto this witness is phase 6
(spec §9), so the lane here stops at the shapes A1.5 names.
"""
import unittest
from pathlib import Path

from c2mix import config
from c2mix.ir.ops import Builder
from c2mix.lower import encode as E
from c2mix.lower import rules
from c2mix.mixfmt import reader
from c2mix.mixfmt.writer import to_str

Q = 3329
ZETA = 31498            # the zeta of golden cut0's first lane, #x7B0A
QINV = 62209 - (1 << 16)

HEADS = {"eqP", "PConst", "PAdd", "PSub", "PMul", "PNeg", "PPow", "bv2nat", "bv2int"}


def shape(term):
    """The term with every symbol replaced by _, keeping structure and constants."""
    def fn(n):
        if isinstance(n, str) and n not in HEADS and not n.lstrip("-").isdigit():
            return "_"
        return None
    return to_str(reader.rewrite(term, fn))


def lane():
    """One butterfly lane: t = zeta*a (16-bit, splits), then m = t*qinv."""
    b = Builder()
    a = b.input("a", 16, True)
    z = b.const(ZETA, 16, True)
    t = b.mul(z, a)                     # L4′: low half is t, high half a witness
    qinv = b.const(QINV, 16, True)
    b.mul(t, qinv)                      # reads t again: L4′ once more
    return b.build()


def skeleton(term):
    """Shape with constant values abstracted too: structure only. PPow exponents stay,
    since they are structure rather than data."""
    def fn(n):
        if isinstance(n, list) and n[:1] == ["PPow"]:
            return ["PPow", n[1], n[2]]
        if isinstance(n, str) and n not in HEADS:
            return "_"
        return None
    return to_str(reader.rewrite(term, fn))


def golden_shapes():
    cfg = config.load()
    f = cfg.golden_root / "pqclean_kyber768_avx2_noAssume" / "cut0.smt2"
    if not f.exists():
        return None
    mix = reader.read(f)
    secs = mix.sections()
    return {skeleton(c.sexpr[1]) for c in secs["alg"]
            if isinstance(c.sexpr, list) and c.sexpr[0] == "assert"}


class GoldenShapeTest(unittest.TestCase):
    def setUp(self):
        prog = lane()
        self.seg = rules.lower(prog, mode=E.BV2INT)
        self.shapes = [shape(t) for t in self.seg.alg]
        self.golden = golden_shapes()

    def test_split_and_bridge_shapes_are_produced(self):
        split = ("(eqP (PAdd (PConst (bv2nat _)) (PMul (PConst (bv2int _)) (PConst 65536)))"
                 " (PMul (PConst 31498) (PConst (bv2int _))))")
        bridge = ("(eqP (PAdd (PConst (bv2int _)) (PMul (PConst (bv2nat _)) (PConst 65536)))"
                  " (PConst (bv2nat _)))")
        self.assertIn(split, self.shapes, self.shapes)
        self.assertIn(bridge, self.shapes, self.shapes)

    @unittest.skipUnless(golden_shapes(), "golden corpus not available")
    def test_every_statement_has_a_golden_counterpart(self):
        """Structure (not constants) of every statement the lane emits also occurs in
        the golden's algebraic section."""
        for t in self.seg.alg:
            self.assertIn(skeleton(t), self.golden,
                          f"structure not used by the golden:\n{skeleton(t)[:200]}")


if __name__ == "__main__":
    unittest.main()
