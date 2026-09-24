import unittest

from c2mix.ir import intervals as iv
from c2mix.ir import interp
from c2mix.ir.ops import Builder, IRError, Value, check


class ValueTest(unittest.TestCase):
    def test_ranges(self):
        self.assertEqual((Value("a", 16, True).lo, Value("a", 16, True).hi), (-32768, 32767))
        self.assertEqual((Value("a", 8, False).lo, Value("a", 8, False).hi), (0, 255))
        with self.assertRaises(IRError):
            Value("a", 129, True)


class CheckTest(unittest.TestCase):
    def test_mixed_signedness_needs_a_bridge(self):
        b = Builder()
        a, c = b.input("a", 16, True), b.input("c", 16, False)
        with self.assertRaises(IRError):
            b.add(a, c)

    def test_shift_amount_must_be_in_range(self):
        b = Builder()
        with self.assertRaises(IRError):
            b.shl(b.input("a", 8, False), 8)

    def test_ssa(self):
        b = Builder()
        a = b.input("a", 8, False)
        b.add(a, a)
        prog = b.build()
        prog.instrs.append(prog.instrs[0])
        with self.assertRaises(IRError):
            check(prog)


class InterpTest(unittest.TestCase):
    def test_wrapping_and_readings(self):
        b = Builder()
        a = b.input("a", 8, True)
        b.add(a, a)
        prog = b.build()
        env = interp.run(prog, {"a": 100})
        self.assertEqual(interp.interpret(env["t0"], 8, True), -56)      # 200 wraps
        self.assertEqual(interp.interpret(env["t0"], 8, False), 200)

    def test_arithmetic_vs_logical_shift(self):
        b = Builder()
        s, u = b.input("s", 8, True), b.input("u", 8, False)
        b.ashr(s, 1)
        b.lshr(u, 1)
        prog = b.build()
        env = interp.run(prog, {"s": -8, "u": 248})
        self.assertEqual(interp.interpret(env["t0"], 8, True), -4)
        self.assertEqual(env["t1"], 124)

    def test_rejects_out_of_range_input(self):
        b = Builder()
        b.input("a", 4, True)
        with self.assertRaises(interp.TrapError):
            interp.run(b.build(), {"a": 8})


class IntervalTest(unittest.TestCase):
    def test_exact_when_it_fits(self):
        b = Builder()
        a = b.input("a", 16, True)
        b.add(a, a)
        prog = b.build()
        an = iv.analyze(prog, {"a": iv.Interval(-3328, 3328)})
        self.assertEqual(an.decisions[0], iv.EXACT)
        self.assertEqual(an.of(prog.instrs[0].result), iv.Interval(-6656, 6656))

    def test_split_when_it_can_overflow(self):
        b = Builder()
        a = b.input("a", 16, True)
        b.mul(a, a)
        prog = b.build()
        an = iv.analyze(prog)
        self.assertEqual(an.decisions[0], iv.SPLIT)
        self.assertEqual(an.of(prog.instrs[0].result), iv.Interval(-32768, 32767))

    def test_force_split(self):
        b = Builder()
        a = b.input("a", 16, True)
        b.add(a, a)
        prog = b.build()
        an = iv.analyze(prog, {"a": iv.Interval(0, 1)}, force_split=True)
        self.assertEqual(an.decisions[0], iv.SPLIT)

    def test_mask_interval_and_site(self):
        b = Builder()
        a = b.input("a", 16, False)
        m = b.const(0xFF, 16, False)
        b.and_(m, a)                       # mask first: the site must still be found
        prog = b.build()
        an = iv.analyze(prog)
        self.assertEqual(iv.mask_site(prog.instrs[1], an.consts), (8, 0))
        self.assertEqual(an.of(prog.instrs[1].result), iv.Interval(0, 255))

    def test_reinterpreting_the_same_bits_widens_the_interval(self):
        """extract of the whole value with a different signedness: same bits, other range."""
        b = Builder()
        a = b.input("a", 8, False)
        b.extract(a, 7, 0, signed=True)
        prog = b.build()
        an = iv.analyze(prog, {"a": iv.Interval(0, 255)})
        self.assertEqual(an.of(prog.instrs[0].result), iv.Interval(-128, 127))

    def test_containment_on_a_run(self):
        b = Builder()
        a = b.input("a", 8, True)
        b.mul(a, a)
        prog = b.build()
        an = iv.analyze(prog, {"a": iv.Interval(-4, 4)})
        env = interp.run(prog, {"a": 3})
        self.assertEqual(iv.check_containment(prog, an, env), [])


if __name__ == "__main__":
    unittest.main()
