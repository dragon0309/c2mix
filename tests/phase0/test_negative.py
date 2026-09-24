"""A0.3: every lint rule has a violation file that triggers that rule and no other."""
import shutil
import sys
import unittest
from pathlib import Path

from c2mix import config
from c2mix.mixfmt import lint

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import make_negative  # noqa: E402

NEG = HERE / "negative"
HAVE_Z3 = shutil.which("z3") is not None
# z3 rejects undeclared symbols as well, so under --z3 the DECL file also fails PARSE.
ALSO_PARSE = {"DECL"}


class NegativeCorpusTest(unittest.TestCase):
    def test_every_rule_has_a_file(self):
        self.assertEqual({f.stem for f in NEG.glob("*.smt2")}, set(lint.RULES))

    def test_files_match_generator(self):
        for code, text in make_negative.generate().items():
            self.assertEqual((NEG / f"{code}.smt2").read_text(), text, code)

    def test_clean_base(self):
        cfg = config.load() if HAVE_Z3 else None
        self.assertEqual(lint.lint_file(HERE / "clean" / "minimal.smt2", "strict", cfg), [])

    def test_static_rules_single_trigger(self):
        for f in sorted(NEG.glob("*.smt2")):
            with self.subTest(rule=f.stem):
                got = {d.code for d in lint.lint_file(f, "strict")}
                self.assertEqual(got, set() if f.stem == "PARSE" else {f.stem})

    @unittest.skipUnless(HAVE_Z3, "z3 not installed")
    def test_with_z3(self):
        cfg = config.load()
        for f in sorted(NEG.glob("*.smt2")):
            with self.subTest(rule=f.stem):
                got = {d.code for d in lint.lint_file(f, "strict", cfg)}
                want = {f.stem} | ({"PARSE"} if f.stem in ALSO_PARSE else set())
                self.assertEqual(got, want)

    def test_severity(self):
        """Profiles: strict makes everything but TRIVIAL-GOAL an error."""
        for code, r in lint.RULES.items():
            self.assertEqual(r.strict, lint.W if code == "TRIVIAL-GOAL" else lint.E, code)
        consumer_errors = {c for c, r in lint.RULES.items() if r.consumer == lint.E}
        self.assertEqual(consumer_errors, {"SET-LOGIC", "POLY-DECL", "POLY-SORT", "PRED", "PVAR",
                                           "GOAL", "SECTIONS", "DECL", "PARSE"})


if __name__ == "__main__":
    unittest.main()
