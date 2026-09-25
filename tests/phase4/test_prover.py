"""Unit tests for the phase 4 machinery: cone slicing and deepening (vc/prover.py), the
split range VC (emit/range.py) and G5 reading every answer of a split file."""
from __future__ import annotations

import shutil
import tempfile
import unittest
from pathlib import Path

from c2mix.emit import range as range_mod
from c2mix.gates import g5
from c2mix.lower.encode import Segment
from c2mix.vc import prover

Z3 = shutil.which("z3")


def bv(w):
    return ["_", "BitVec", str(w)]


def model_with(statements, premises=(), sorts=None):
    seg = Segment()
    for name, w in (sorts or {}).items():
        seg.declare(name, bv(w))
    seg.bv.extend(statements)
    return prover.RangeModel(seg, list(premises))


class ConeTests(unittest.TestCase):
    def setUp(self):
        # y = x + 1, z = y * 2, u = x * 3 (unrelated to z), premise on x
        self.m = model_with(
            [["=", "y", ["bvadd", "x", "#x01"]],
             ["=", "z", ["bvmul", "y", "#x02"]],
             ["=", "u", ["bvmul", "x", "#x03"]]],
            premises=[["bvult", "x", "#x10"]],
            sorts={"x": 8, "y": 8, "z": 8, "u": 8})

    def text(self, stmts):
        return [self.m.text[i] for i in stmts]

    def test_a_definition_is_reached_only_through_what_it_defines(self):
        names, stmts = self.m.cone(["=", "z", "#x00"])
        self.assertEqual(names, ["x", "y", "z"])
        body = " ".join(self.text(stmts))
        self.assertIn("(bvult x #x10)", body)          # the premise touches x
        self.assertNotIn("u", names)                   # u uses x but does not constrain it

    def test_depth_leaves_the_far_symbols_free(self):
        names, stmts = self.m.cone(["=", "z", "#x00"], depth=1)
        self.assertEqual(names, ["y", "z"])            # y declared, its definition left out
        self.assertEqual(len(stmts), 1)
        self.assertEqual(self.m.cone(["=", "z", "#x00"], depth=9), self.m.cone(["=", "z", "#x00"]))


@unittest.skipUnless(Z3, "z3 not installed")
class ProveTests(unittest.TestCase):
    def test_depths_and_results(self):
        # l = low byte of (x + (-x)) is always 0, whatever x is; h is not constant
        m = model_with(
            [["=", "a", ["bvadd", "p", "q"]],
             ["=", "x", ["bvmul", "a", "a"]],
             ["=", "n", ["bvneg", "x"]],
             ["=", "l", ["bvadd", "x", "n"]],
             ["=", "h", ["bvadd", "x", "#x01"]]],
            sorts={"p": 8, "q": 8, "a": 8, "x": 8, "n": 8, "l": 8, "h": 8})
        claims = [["=", "l", "#x00"], ["=", "h", "#x00"]]
        got = prover.prove_all(m, claims, Z3, 5.0, depths=(1, 2, None))
        self.assertEqual(got, [True, False])
        self.assertEqual(m.depth_of[prover._key(claims[0])], 2)   # x free is enough


class SplitTests(unittest.TestCase):
    def test_partition_keeps_shared_obligations_together(self):
        seg = Segment()
        for n in ("a", "b", "c", "d", "e"):
            seg.declare(n, bv(8))
        seg.bv += [["=", "c", ["bvadd", "a", "#x01"]], ["=", "d", ["bvadd", "b", "#x01"]],
                   ["=", "e", ["bvadd", "c", "#x01"]]]
        seg.safety += [["bvult", "c", "#xff"], ["bvult", "d", "#xff"], ["bvult", "e", "#xff"]]

        class VC:
            pass
        vc = VC()
        vc.seg, vc.premise_range, vc.goal_range, vc.hints, vc.depths = seg, [], [], [], {}
        parts = range_mod.partition(vc, 8)
        groups = sorted(sorted(range_mod.to_str(g) for g, _ in goals) for goals, *_ in parts)
        self.assertEqual(len(parts), 2)                # {c, e} share c's definition; d alone
        self.assertEqual(groups, [["(bvult c #xff)", "(bvult e #xff)"], ["(bvult d #xff)"]])
        text = range_mod.render_part(parts[0][0], parts[0][3])
        self.assertEqual(text.count("(check-sat)"), len(parts[0][0]))
        self.assertEqual(text.count("(reset)"), len(parts[0][0]) - 1)


@unittest.skipUnless(Z3, "z3 not installed")
class G5Tests(unittest.TestCase):
    def test_every_answer_of_a_split_file_counts(self):
        d = Path(tempfile.mkdtemp())
        good = ("(set-logic QF_BV)\n(declare-const a (_ BitVec 4))\n"
                "(assert (not (= (bvadd a #x0) a)))\n(check-sat)\n")
        bad = ("(set-logic QF_BV)\n(declare-const a (_ BitVec 4))\n"
               "(assert (not (= a #x0)))\n(check-sat)\n")
        (d / "ok.range.0.smt2").write_text(good + "(reset)\n" + good)
        (d / "no.range.0.smt2").write_text(good + "(reset)\n" + bad)
        self.assertEqual(g5.check_file(d / "ok.range.0.smt2", Z3), (True, "unsat ×2"))
        ok, got = g5.check_file(d / "no.range.0.smt2", Z3)
        self.assertFalse(ok)
        self.assertIn("1/2 not unsat", got)


if __name__ == "__main__":
    unittest.main()
