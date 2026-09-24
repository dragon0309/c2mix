import unittest
from pathlib import Path

from c2mix.mixfmt import reader, writer
from c2mix.mixfmt.reader import Command, Comment, ParseError

HERE = Path(__file__).resolve().parent
MINIMAL = HERE / "clean" / "minimal.smt2"


class ReaderTest(unittest.TestCase):
    def test_atoms_and_lists(self):
        m = reader.parse('(assert (eqP (PVar "a""b") |q x|)) ; tail\n(exit)\n')
        self.assertEqual(m.items[0].sexpr, ["assert", ["eqP", ["PVar", '"a""b"'], "|q x|"]])
        self.assertIsInstance(m.items[1], Comment)
        self.assertEqual(m.items[1].text, "; tail")
        self.assertEqual(m.items[2].line, 2)

    def test_line_numbers_across_multiline_command(self):
        m = reader.parse("(a\n b\n c)\n(d)\n")
        self.assertEqual([c.line for c in m.commands()], [1, 4])

    def test_inner_comment_recorded(self):
        m = reader.parse("(a ; x\n b)\n")
        self.assertEqual(m.items[0].sexpr, ["a", "b"])
        self.assertEqual([c.text for c in m.inner_comments], ["; x"])

    def test_unbalanced(self):
        with self.assertRaises(ParseError):
            reader.parse("(a (b)\n")
        with self.assertRaises(ParseError):
            reader.parse("(a))\n")

    def test_deep_nesting_is_not_recursive(self):
        depth = 20000
        text = "(assert " + "(PAdd " * depth + "(PConst 1)" + " (PConst 2))" * depth + ")\n"
        m = reader.parse(text)
        self.assertEqual(writer.write(m), text)

    def test_sections(self):
        m = reader.read(MINIMAL)
        s = m.sections()
        self.assertIsNotNone(s)
        self.assertEqual([c.head for c in s["header"]], ["set-info", "set-logic"])
        self.assertEqual([c.head for c in s["check"]], ["check-sat", "exit"])
        self.assertEqual(len([c for c in s["post"] if isinstance(c, Command)]), 1)

    def test_sections_need_trailing_space(self):
        text = MINIMAL.read_text().replace("program \n", "program\n")
        self.assertIsNone(reader.parse(text).sections())


class RewriteTest(unittest.TestCase):
    def test_bottom_up(self):
        t = ["f", ["PPow", "g", "2"], ["h", ["PPow", "g", "2"], "x"]]
        out = reader.rewrite(t, lambda n: "g" if n == ["PPow", "g", "2"] else None)
        self.assertEqual(out, ["f", "g", ["h", "g", "x"]])
        self.assertEqual(t[1], ["PPow", "g", "2"])          # input untouched

    def test_atoms_and_root(self):
        self.assertEqual(reader.rewrite(["a", "b"], lambda n: "B" if n == "b" else None), ["a", "B"])
        self.assertEqual(reader.rewrite(["a"], lambda n: "z" if n == ["a"] else None), "z")

    def test_deep(self):
        t = "x"
        for _ in range(20000):
            t = ["PNeg", t]
        out = reader.rewrite(t, lambda n: "y" if n == "x" else None)
        self.assertEqual(writer.to_str(out).count("y"), 1)


class WriterTest(unittest.TestCase):
    def test_roundtrip_bytes(self):
        text = MINIMAL.read_text()
        self.assertEqual(writer.write(reader.parse(text)), text)

    def test_normalize_ignores_whitespace_only(self):
        a = "(assert  (= a\n b))\n; c \n"
        b = "(assert (= a b))\n; c \n"
        self.assertEqual(writer.normalize(a), writer.normalize(b))
        self.assertNotEqual(writer.normalize(a), writer.normalize(b.replace("; c ", "; c")))

    def test_to_str(self):
        self.assertEqual(writer.to_str(["a", ["b", []], "c"]), "(a (b ()) c)")


if __name__ == "__main__":
    unittest.main()
