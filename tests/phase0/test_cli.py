import contextlib
import io
import shutil
import tempfile
import unittest
from pathlib import Path

from c2mix import cli

HERE = Path(__file__).resolve().parent
TMP = HERE.parents[1] / "work" / "tmp"          # stay inside the c2mix tree
MINIMAL = HERE / "clean" / "minimal.smt2"


def _tmpdir() -> Path:
    TMP.mkdir(parents=True, exist_ok=True)
    return TMP


def run(*argv) -> tuple[int, str]:
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        code = cli.main(list(argv))
    return code, buf.getvalue()


class RoundtripCliTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(dir=_tmpdir()))
        self.src = self.tmp / "in" / "minimal.smt2"
        self.src.parent.mkdir()
        shutil.copy(MINIMAL, self.src)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def test_absolute_input_stays_inside_outdir(self):
        code, out = run("roundtrip", "-o", str(self.tmp / "out"), str(self.src.resolve()))
        self.assertEqual(code, 0, out)
        self.assertTrue((self.tmp / "out" / "minimal.smt2").exists())
        self.assertEqual(self.src.read_text(), MINIMAL.read_text())

    def test_refuses_to_overwrite_input(self):
        self.src.write_text(MINIMAL.read_text().replace("(assert true)", "(assert  true)"))
        before = self.src.read_text()
        code, out = run("roundtrip", "-o", str(self.src.parent), str(self.src))
        self.assertEqual(code, 2, out)
        self.assertEqual(self.src.read_text(), before)


class LintCliTest(unittest.TestCase):
    def test_strict_clean_and_error_exit(self):
        self.assertEqual(run("lint", str(MINIMAL))[0], 0)
        code, out = run("lint", str(HERE / "negative" / "GOAL.smt2"))
        self.assertEqual(code, 1)
        self.assertIn("E-GOAL", out)

    def test_baseline_mismatch(self):
        tmp = Path(tempfile.mkdtemp(dir=_tmpdir()))
        try:
            base = tmp / "b.json"
            f = str(HERE / "negative" / "TRIVIAL-GOAL.smt2")
            self.assertEqual(run("lint", "--write-baseline", str(base), f)[0], 0)
            self.assertEqual(run("lint", "--baseline", str(base), f)[0], 0)
            code, out = run("lint", "--baseline", str(base), str(MINIMAL))
            self.assertEqual(code, 1, out)
        finally:
            shutil.rmtree(tmp)


if __name__ == "__main__":
    unittest.main()
