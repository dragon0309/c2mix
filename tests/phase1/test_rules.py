"""Shapes the lowering must produce (spec §6.3), and its determinism (M9)."""
import unittest

from c2mix.ir import intervals as iv
from c2mix.ir import interp
from c2mix.ir.ops import Builder
from c2mix.lower import encode as E
from c2mix.lower import evaluate, rules
from c2mix.mixfmt.writer import to_str


def lower_one(build, pre=None, mode=E.ALIAS, force_split=False):
    b = Builder()
    prog = build(b)
    an = iv.analyze(prog, pre, force_split)
    return prog, an, rules.lower(prog, an, mode=mode)


def algs(seg):
    return [to_str(t) for t in seg.alg]


class RuleShapeTest(unittest.TestCase):
    def test_L3_exact_has_a_safety_obligation(self):
        prog, an, seg = lower_one(lambda b: (b.add(b.input("a", 16, True), b.input("b", 16, True)),
                                             b.build())[1],
                                  {"a": iv.Interval(-100, 100), "b": iv.Interval(-100, 100)})
        self.assertEqual(an.decisions[0], iv.EXACT)
        self.assertIn("(eqP (PConst s__t0) (PAdd (PConst s__a) (PConst s__b)))", algs(seg))
        self.assertEqual(len(seg.safety), 1)

    def test_L3p_unsigned_subtraction_borrows_negatively(self):
        """a − b can go below zero even for unsigned operands, so the borrow enters
        with a minus sign, the way the OpenSSL golden writes it."""
        _, an, seg = lower_one(lambda b: (b.sub(b.input("a", 16, False), b.input("b", 16, False)),
                                          b.build())[1])
        self.assertEqual(an.decisions[0], iv.SPLIT)
        self.assertEqual(algs(seg)[0],
                         "(eqP (PSub (PConst (bv2nat a)) (PConst (bv2nat b))) "
                         "(PAdd (PMul (PConst s__wh0) (PConst 65536)) (PConst (bv2nat t0))))")
        self.assertEqual(seg.safety, [])

    def test_L4p_matches_the_golden_split(self):
        _, _, seg = lower_one(lambda b: (b.mul(b.input("a", 16, True), b.input("b", 16, True)),
                                         b.build())[1], mode=E.BV2INT)
        self.assertIn("(eqP (PAdd (PConst (bv2nat t0)) (PMul (PConst (bv2int wh0)) (PConst 65536)))"
                      " (PMul (PConst (bv2int a)) (PConst (bv2int b))))", algs(seg))

    def test_L13_bitwise_is_algebraically_free(self):
        _, _, seg = lower_one(lambda b: (b.xor(b.input("a", 8, False), b.input("b", 8, False)),
                                         b.build())[1])
        self.assertEqual(seg.alg, [])
        self.assertEqual([n["warning"] for n in seg.notes if "warning" in n], [rules.W_ALG_FREE])

    def test_L12_adds_the_idempotence_of_the_condition(self):
        def build(b):
            c = b.input("c", 1, False)
            b.ite(c, b.input("x", 8, True), b.input("y", 8, True))
            return b.build()
        _, _, seg = lower_one(build)
        self.assertIn("(eqP (PMul (PConst (bv2nat c)) (PConst (bv2nat c))) (PConst (bv2nat c)))",
                      algs(seg))

    def test_constants_are_inlined_not_declared(self):
        def build(b):
            b.add(b.input("a", 16, True), b.const(-1044, 16, True))
            return b.build()
        _, _, seg = lower_one(build, {"a": iv.Interval(0, 10)})
        self.assertNotIn("t0", seg.decls)
        self.assertIn("(- 1044)", to_str(seg.alg[0]))

    def test_alias_definition_is_two_complement(self):
        _, _, seg = lower_one(lambda b: (b.neg(b.input("a", 8, True)), b.build())[1],
                              {"a": iv.Interval(-1, 1)})
        self.assertIn("(= s__a (- (bv2nat a) (* 256 (bv2nat ((_ extract 7 7) a)))))",
                      [to_str(t) for t in seg.bv])

    def test_bridge_is_emitted_once_per_value(self):
        """Reading one value in both signednesses relates the two atoms once (L10),
        however often it is read."""
        from c2mix.ir.ops import Value
        seg = E.Segment()
        enc = E.Encoder(seg)
        v = Value("v", 16, True, "input")
        for _ in range(3):
            self.assertEqual(enc.read(v, True), "s__v")
            self.assertEqual(enc.read(v, False), ["bv2nat", "v"])
        self.assertEqual(len(seg.bridge_alg), 1)
        self.assertEqual(algs(seg), ["(eqP (PAdd (PConst s__v) (PMul (PConst (bv2nat wb0)) "
                                     "(PConst 65536))) (PConst (bv2nat v)))"])

    def test_constant_needs_no_bridge(self):
        """Both readings of a constant are literals (L1), so there is nothing to relate."""
        from c2mix.ir.ops import Value
        seg = E.Segment()
        enc = E.Encoder(seg)
        c = Value("c", 8, True, "const")
        enc.set_const(c, -1)
        self.assertEqual((enc.read(c, True), enc.read(c, False)), (["-", "1"], "255"))
        self.assertEqual((seg.alg, seg.bv, seg.decls), ([], [], {}))

    def test_deterministic(self):
        def build(b):
            a, c = b.input("a", 32, True), b.input("c", 32, True)
            t = b.mul(a, c)
            u = b.ashr(t, 7)
            return (b.sub(u, a), b.build())[1]
        outs = set()
        for _ in range(3):
            _, _, seg = lower_one(build)
            outs.add("\n".join(algs(seg) + [to_str(t) for t in seg.bv]))
        self.assertEqual(len(outs), 1)


class StatementsHoldOnRunsTest(unittest.TestCase):
    """The small-scale version of A1.3: statements are true on concrete runs."""

    def check(self, build, pre, inputs):
        prog, an, seg = lower_one(build, pre)
        widths = evaluate.widths_of(seg)
        patterns = interp.run(prog, inputs)
        env = evaluate.Env({k: v for k, v in patterns.items() if k in widths}, widths)
        evaluate.solve_definitions(seg, env)
        self.assertEqual(evaluate.check_segment(seg, env), [])
        self.assertEqual(iv.check_containment(prog, an, patterns), [])

    def test_montgomery_like_chain(self):
        def build(b):
            a = b.input("a", 16, True)
            z = b.const(31498, 16, True)
            t = b.mul(z, a)                      # splits
            qinv = b.const(62209 - (1 << 16), 16, True)
            m = b.mul(t, qinv)                   # splits, reads t signed
            q = b.const(3329, 16, True)
            return (b.mul(m, q), b.build())[1]
        for a in (-3328, -1, 0, 1, 1234, 3328):
            self.check(build, {"a": iv.Interval(-3328, 3328)}, {"a": a})

    def test_unsigned_borrow_chain(self):
        def build(b):
            a, c = b.input("a", 64, False), b.input("c", 64, False)
            d = b.sub(a, c)
            return (b.and_(d, b.const((1 << 32) - 1, 64, False)), b.build())[1]
        for a, c in ((0, 1), (5, 5), (2**64 - 1, 1), (7, 2**63)):
            self.check(build, None, {"a": a, "c": c})


if __name__ == "__main__":
    unittest.main()
