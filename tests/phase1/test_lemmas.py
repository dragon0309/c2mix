"""A1.1/A1.2 in the fast sizes: the full sweep lives in tests/phase1/accept.py.

Two variants of every lemma (see lemmas.render_bv):
  mixed — exactly the statements c2mix emits (bv2nat, Int aliases). z3 can only do
          these at width 4; mixing bit-vectors with integer arithmetic is precisely
          what extend_z3 exists for.
  bv    — the same lemma stated in QF_BV at a width wide enough that the two are
          equivalent, which z3 bit-blasts quickly. This carries the wider widths.
"""
import shutil
import unittest

from c2mix.lower import lemmas

HAVE_Z3 = shutil.which("z3") is not None
RULES_EXPECTED = {"L3", "L3'", "L4", "L4'", "L6", "L6'", "L7", "L8", "L9", "L9'",
                  "L9m", "L10", "L11", "L12", "L13n"}


def run(items, timeout=30):
    return lemmas.check_all(items, jobs=12, timeout=timeout)


class CatalogueTest(unittest.TestCase):
    def test_rules_covered(self):
        got = {L.rule for L in lemmas.generate(widths=(16,))}
        self.assertEqual(got, RULES_EXPECTED)

    def test_every_lemma_has_at_least_three_mutants(self):
        for L in lemmas.generate(widths=(16,)):
            self.assertGreaterEqual(len(lemmas.mutate(L)), 3, L.name)

    def test_poly_to_int_rejects_indeterminates(self):
        with self.assertRaises(ValueError):
            lemmas.poly_to_int(["eqP", ["PVar", '"x"'], ["PConst", "1"]])


@unittest.skipUnless(HAVE_Z3, "z3 not installed")
class LemmaCheckTest(unittest.TestCase):
    def test_mixed_encoding_at_width_4(self):
        """A1.1 on the encoding c2mix really emits."""
        base = [L for L in lemmas.generate(widths=(4,)) if "128" not in L.name]
        items = base + [m for L in base for m in lemmas.mutate(L)]
        bad = [(L.name, L.expect, got) for L, ok, got in run(items) if not ok]
        self.assertEqual(bad, [])

    def test_qf_bv_image_at_8_and_16(self):
        """A1.1/A1.2 at wider widths, via the QF_BV image."""
        base = [L for L in lemmas.generate(widths=(8, 16)) if "128" not in L.name]
        items = [lemmas.render_bv(L) for L in base]
        items += [lemmas.render_bv(m) for L in base for m in lemmas.mutate(L)]
        bad = [(L.name, L.expect, got) for L, ok, got in run(items) if not ok]
        self.assertEqual(bad, [])

    def test_a_broken_rule_would_be_caught(self):
        """Sanity check on the checker itself: a wrong statement must come out sat."""
        L = [x for x in lemmas.generate(widths=(8,)) if x.name == "L3.add.w8.s"][0]
        broken = lemmas.render(L.segment, "broken", "L3")
        broken.text = broken.text.replace("(+ s__a s__b)", "(+ s__a s__a)")
        broken.expect = "sat"
        ok, got = lemmas.check(broken)
        self.assertTrue(ok, got)


if __name__ == "__main__":
    unittest.main()
