"""A2.1: the specification self-checks S1–S4, and the mutations they must catch."""
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "targets"))

import t2a_ntt8                                      # noqa: E402
import t2c_montgomery                                # noqa: E402
from c2mix.ir.trace import ENTRY_POINT, Point        # noqa: E402
from c2mix.lib import ntt                            # noqa: E402
from c2mix.spec import dsl                           # noqa: E402
from c2mix.spec.check import check_spec              # noqa: E402


class DslTest(unittest.TestCase):
    def test_chained_range(self):
        t = dsl.Target("f", args={"a": dsl.In("int32_t")})
        a = t.arg("a")
        r = dsl.rng(0 <= a.entry < 100)
        self.assertEqual((r.lo.value, r.hi.value), (0, 100))
        self.assertIsInstance(r.expr, dsl.Ref)

    def test_range_needs_both_bounds(self):
        t = dsl.Target("f", args={"a": dsl.In("int32_t")})
        with self.assertRaises(ValueError):
            dsl.rng(t.arg("a").entry < 100)

    def test_abs_lt(self):
        t = dsl.Target("f", args={"a": dsl.In("int32_t")})
        r = dsl.abs_lt(t.arg("a").entry, 17)
        self.assertEqual((r.lo.a.b.value, r.hi.value), (17, 17))

    def test_time_application_is_recursive(self):
        t = dsl.Target("f", args={"r": dsl.InOut(dsl.Array("int16_t", 4))})
        x = dsl.Indet("x")
        p = dsl.poly([t.arg("r")[i] for i in range(4)], x).exit
        self.assertTrue(all(ref.time.kind == "exit" for ref in p.refs()))
        self.assertEqual(len(p.indets()), 3)


class SelfCheckTest(unittest.TestCase):
    def test_clean_targets(self):
        for mod in (t2a_ntt8, t2c_montgomery):
            trace, target = mod.build()
            self.assertEqual([str(f) for f in check_spec(target, trace)], [], mod.__name__)

    def test_s1_catches_a_reference_that_is_not_live(self):
        trace, target = t2c_montgomery.build()
        r = target.arg("r")
        target.pre(range=[dsl.abs_lt(r.entry, 10)])     # r only exists at the exit
        got = [str(f) for f in check_spec(target, trace)]
        self.assertTrue(any(f.startswith("S1") for f in got), got)

    def test_s1_catches_an_unknown_cut(self):
        trace, target = t2c_montgomery.build()
        a = target.arg("a")
        target.pre(range=[dsl.abs_lt(a.at(Point("cut", "nope", 1)), 10)])
        got = [str(f) for f in check_spec(target, trace)]
        self.assertTrue(any("does not contain" in f for f in got), got)

    def test_s2_catches_three_moduli(self):
        trace, target = t2c_montgomery.build()
        a, r = target.arg("a"), target.arg("r")
        target.post(alg=[dsl.eqmod(r.exit, a.entry, [3, 5, 7])])
        got = [str(f) for f in check_spec(target, trace)]
        self.assertTrue(any(f.startswith("S2") for f in got), got)

    def test_s4_catches_a_ghost_reading_a_later_value(self):
        trace, target = t2c_montgomery.build()
        g = target.ghost("bad", target.arg("r").exit)
        target.post(alg=[dsl.eq(g, target.arg("a").entry)])
        got = [str(f) for f in check_spec(target, trace)]
        self.assertTrue(any(f.startswith("S4") for f in got), got)

    def test_s4_catches_an_unbound_ghost(self):
        trace, target = t2c_montgomery.build()
        target.post(alg=[dsl.eq(dsl.Ghost("nope"), target.arg("a").entry)])
        got = [str(f) for f in check_spec(target, trace)]
        self.assertTrue(any("never bound" in f for f in got), got)

    def test_ghost_bound_twice(self):
        _, target = t2c_montgomery.build()
        target.ghost("g", target.arg("a").entry)
        with self.assertRaises(ValueError):
            target.ghost("g", target.arg("a").entry)


class ScheduleTest(unittest.TestCase):
    """S3, on the schedule the NTT target uses."""

    def test_schedule_is_consistent(self):
        layers = t2a_ntt8.schedule()
        self.assertEqual([len(l) for l in layers], [2, 4, 8])
        self.assertEqual([b.deg for b in layers[-1]], [1] * 8)

    def test_wrong_zeta_is_caught(self):
        zetas = list(t2a_ntt8.ZETAS[1:])
        zetas[1] = (zetas[1] + t2a_ntt8.MONT.R) % (t2a_ntt8.Q * t2a_ntt8.MONT.R)
        with self.assertRaises(ntt.ScheduleError):
            ntt.ct_schedule(8, t2a_ntt8.Q, zetas, R=t2a_ntt8.MONT.R, layers=3)

    def test_missing_block_is_caught(self):
        layers = [list(l) for l in t2a_ntt8.schedule()]
        layers[-1] = layers[-1][:-1]
        with self.assertRaises(ntt.ScheduleError):
            ntt.check_schedule(8, t2a_ntt8.Q, layers)

    def test_leaves_must_multiply_to_xn_plus_1(self):
        layers = [list(l) for l in t2a_ntt8.schedule()]
        last = layers[-1]
        layers[-1] = last[:-1] + [ntt.Block(last[-1].lo, last[-1].hi, 1,
                                            (last[-1].zeta + 1) % t2a_ntt8.Q)]
        with self.assertRaises(ntt.ScheduleError):
            ntt.check_schedule(8, t2a_ntt8.Q, layers)


if __name__ == "__main__":
    unittest.main()
