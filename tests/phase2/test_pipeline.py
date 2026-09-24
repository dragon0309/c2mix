"""VC assembly and emission (spec §7): segments, premises, carrying, formats."""
import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "targets"))

import t2a_ntt8                                          # noqa: E402
import t2c_montgomery                                    # noqa: E402
from c2mix import config, pipeline                       # noqa: E402
from c2mix.gates import g9                               # noqa: E402
from c2mix.ir.trace import ENTRY_POINT, EXIT_POINT       # noqa: E402
from c2mix.mixfmt import lint, reader                    # noqa: E402
from c2mix.vc import carry                               # noqa: E402
from c2mix.vc.assemble import Options, assemble, segment_spans   # noqa: E402

TMP = HERE.parents[1] / "work" / "tmp" / "phase2"


class SegmentTest(unittest.TestCase):
    def test_one_segment_per_cut(self):
        trace, _ = t2a_ntt8.build()
        spans = segment_spans(trace)
        self.assertEqual(len(spans), 4)                   # entry -> 3 cuts -> exit
        self.assertEqual(spans[0][0], ENTRY_POINT)
        self.assertEqual(spans[-1][1], EXIT_POINT)
        self.assertEqual([lo for _, _, (lo, hi) in spans],
                         [0] + [hi for _, _, (lo, hi) in spans[:-1]])

    def test_values_from_earlier_segments_are_declared_not_defined(self):
        trace, target = t2a_ntt8.build()
        vcs = assemble(trace, target, Options(hints="off"))
        vc = vcs[1]
        defined = {t[1] for t in vc.seg.bv if isinstance(t, list) and t[0] == "="}
        consts = {ins.result.name for ins in trace.prog.instrs if ins.op == "const"}
        read = {a.name for ins in trace.prog.instrs[vc.span[0]:vc.span[1]] for a in ins.args}
        inputs = read - defined - consts          # constants are inlined, not declared (L1)
        self.assertTrue(inputs)
        for name in inputs:
            self.assertIn(name, vc.seg.decls, f"{name} is read but never declared")
        for name in consts & read:
            self.assertNotIn(name, vc.seg.decls, f"constant {name} should be inlined")


class CarryTest(unittest.TestCase):
    def test_relevant_carries_nothing_when_nothing_is_relevant(self):
        trace, target = t2a_ntt8.build()
        vcs = assemble(trace, target, Options(hints="off", carry="relevant"))
        self.assertEqual([len(vc.carried) for vc in vcs], [0, 0, 0, 0])

    def test_all_carries_every_earlier_assertion(self):
        trace, target = t2a_ntt8.build()
        vcs = assemble(trace, target, Options(hints="off", carry="all"))
        self.assertEqual(len(vcs[0].carried), 0)
        self.assertGreater(len(vcs[1].carried), 0)
        self.assertGreater(len(vcs[3].carried), len(vcs[1].carried))

    def test_carried_facts_come_from_earlier_points(self):
        trace, target = t2a_ntt8.build()
        spans = segment_spans(trace)
        for i in range(len(spans)):
            _, _, prov = carry.carried_facts(trace, target, i, spans, "all")
            earlier = {str(p) for p, _, _ in spans[:i]}
            self.assertTrue(all(src in earlier for src, _ in prov))


class EmitTest(unittest.TestCase):
    def setUp(self):
        self.cfg = config.load()
        TMP.mkdir(parents=True, exist_ok=True)

    def build(self, mod, **kw):
        trace, target = mod.build()
        return pipeline.build(trace, target, TMP / mod.__name__, mod.__name__,
                              Options(**kw), self.cfg)

    def test_output_passes_strict_lint(self):
        b = self.build(t2c_montgomery, hints="emit")
        for f in b.files:
            if f.suffix == ".smt2" and "range" not in f.name:
                diags = lint.lint_file(f, "strict", self.cfg)
                self.assertEqual([d.render() for d in diags], [], f.name)

    def test_range_file_is_qf_bv_only(self):
        b = self.build(t2c_montgomery, hints="emit")
        rng = [f for f in b.files if "range" in f.name][0]
        mix = reader.read(rng)
        self.assertEqual(mix.commands()[0].sexpr, ["set-logic", "QF_BV"])
        text = rng.read_text()
        for poly in ("eqP", "PConst", "bv2nat", "Poly"):
            self.assertNotIn(poly, text, f"{poly} leaked into the range VC")

    def test_trivial_goal_is_spelled_out(self):
        """M6: a cut with no algebraic goal still writes (not (and true true))."""
        trace, target = t2c_montgomery.build()
        target.post_algs.clear()
        vcs = assemble(trace, target, Options(hints="off"))
        from c2mix.emit import mix as mix_mod
        text = mix_mod.render(vcs[0])
        self.assertIn("(assert (not (and true true)))", text)
        self.assertTrue(vcs[0].trivial)

    def test_manifest_records_decisions_and_hints(self):
        b = self.build(t2c_montgomery, hints="emit")
        man = json.loads((b.out_dir / "manifest.json").read_text())
        cut = man["cuts"][0]
        self.assertIn("EXACT", cut["decisions"])
        self.assertTrue(cut["hints"]["proved"])
        self.assertEqual(cut["hints"]["proved"], cut["hints"]["emitted"])
        self.assertFalse(man["ab_only"])
        self.assertEqual(g9.check(man), [])

    def test_hints_omitted_are_still_recorded(self):
        b = self.build(t2c_montgomery, hints="omit")
        man = json.loads((b.out_dir / "manifest.json").read_text())
        cut = man["cuts"][0]
        self.assertTrue(cut["hints"]["proved"])
        self.assertEqual(cut["hints"]["emitted"], [])
        text = (b.out_dir / "cut0.smt2").read_text()
        self.assertNotIn("(PConst 0)", text.split("; postcondition")[0].split("; algebraic")[1])

    def test_ab_only_is_flagged(self):
        b = self.build(t2c_montgomery, hints="omit", int_encoding="bv2int")
        man = json.loads((b.out_dir / "manifest.json").read_text())
        self.assertTrue(man["ab_only"])


if __name__ == "__main__":
    unittest.main()
