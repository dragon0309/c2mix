import re
import unittest

from c2mix import config
from c2mix.mixfmt.prelude import POLY_PRELUDE
from c2mix.oracle import inject_prelude

SRC = config.load().path("../extend_z3/src/smt2_frontend.cpp")


class PreludeTest(unittest.TestCase):
    @unittest.skipUnless(SRC.exists(), "extend_z3 source not available")
    def test_matches_extend_z3(self):
        m = re.search(r'poly_prelude = R"PRE\((.*?)\)PRE"', SRC.read_text(), re.S)
        self.assertIsNotNone(m)
        self.assertEqual(m.group(1), POLY_PRELUDE)

    def test_injection_point(self):
        raw = "(set-info :x 1)\n(set-logic ALL)\n(assert true)\n"
        script, after, n = inject_prelude(raw)
        lines = script.split("\n")
        self.assertEqual(after, 2)
        self.assertEqual(lines[1], "(set-logic ALL)")
        self.assertEqual(lines[after + n], "(assert true)")

    def test_no_injection_when_declared(self):
        raw = "(set-logic ALL)\n(declare-datatype Poly ())\n"
        self.assertEqual(inject_prelude(raw), (raw, 0, 0))


if __name__ == "__main__":
    unittest.main()
