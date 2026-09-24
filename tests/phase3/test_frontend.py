"""Unit tests for the C frontend (spec §5.4, §5.5). Fast: no bin/main, no z3."""
from __future__ import annotations

import subprocess
import textwrap
import unittest
from pathlib import Path

from c2mix.frontend import execute, harness, llparse
from c2mix.frontend.toolchain import Toolchain
from c2mix.ir import interp
from c2mix.spec import dsl

ROOT = Path(__file__).resolve().parents[2]
TMP = ROOT / "work" / "tmp" / "phase3"          # stay inside the c2mix tree (W1)


def compile_body(tmp: Path, source: str, name: str = "t") -> llparse.Module:
    tmp.mkdir(parents=True, exist_ok=True)
    src = tmp / f"{name}.c"
    src.write_text(textwrap.dedent(source))
    ll = Toolchain().build_ir([src], tmp / "ir", includes=(ROOT / "include",))
    return llparse.parse(ll.read_text(), str(ll))


class ParserTest(unittest.TestCase):
    def test_types_and_sizes(self):
        lx = llparse.Lexer("[4 x i16]")
        ty = llparse.parse_type(lx)
        self.assertEqual(str(ty), "[4 x i16]")
        self.assertEqual(ty.size, 8)
        self.assertEqual(llparse.parse_type(llparse.Lexer("i128")).size, 16)

    def test_vector_type_is_refused(self):
        with self.assertRaises(llparse.ParseError) as cm:
            llparse.parse_type(llparse.Lexer("<8 x i16>"))
        self.assertEqual(cm.exception.code, "E-VECTOR")

    def test_float_type_is_refused(self):
        with self.assertRaises(llparse.ParseError) as cm:
            llparse.parse_type(llparse.Lexer("double"))
        self.assertEqual(cm.exception.code, "E-FLOAT")

    def test_division_is_refused_with_its_code(self):
        with self.assertRaises(llparse.ParseError) as cm:
            llparse.parse_instr("%3 = udiv i32 %1, %2", 7)
        self.assertEqual(cm.exception.code, "E-DIV")

    def test_instruction_round_trip(self):
        for text in ("%3 = add i32 %1, %2",
                     "%4 = trunc i32 %3 to i16",
                     "%5 = icmp slt i32 %3, 4",
                     "%6 = select i1 %5, i16 %4, i16 0",
                     "store i16 %4, ptr %7, align 2",
                     "%8 = load i16, ptr %7, align 2, !dbg !3",
                     "%9 = getelementptr [8 x i16], ptr @z, i64 0, i64 %2",
                     "%10 = phi i16 [ %4, %1 ], [ %8, %2 ]",
                     "br i1 %5, label %6, label %7",
                     "ret void"):
            with self.subTest(text=text):
                self.assertEqual(llparse.render_instr(llparse.parse_instr(text, 1)), text)

    def test_poison_flags_are_parsed_and_kept(self):
        ins = llparse.parse_instr("%3 = add nsw i32 %1, %2", 1)
        self.assertIn("nsw", ins.flags)
        self.assertEqual(llparse.render_instr(ins), "%3 = add nsw i32 %1, %2")


class ExecutorTest(unittest.TestCase):
    tmp = TMP / "unit"

    def test_poison_flag_is_refused(self):
        ins = llparse.parse_instr("%3 = add nsw i32 %1, %2", 5)
        ex = execute.Executor(llparse.Module(), "f")
        fr = execute.Frame(llparse.Function("@f", llparse.VOID, (), (), [], False, ""), {}, {})
        with self.assertRaises(execute.ExecError) as cm:
            ex.step(fr, ins)
        self.assertEqual(cm.exception.code, "E-POISON-FLAG")

    def test_constant_control_flow_unrolls(self):
        mod = compile_body(self.tmp / "unroll", """
            #include <stdint.h>
            #include "c2mix.h"
            void c2mix_body(void) {
              uint32_t o = 0, x = 0;
              c2mix_register("o", &o, 1, sizeof o, 0);
              c2mix_register("x", &x, 1, sizeof x, 0);
              c2mix_input("x");
              for (int i = 0; i < 3; i++) o = o + x;
              c2mix_done();
            }
            """, "unroll")
        trace, stats = execute.execute(mod, "c2mix_body")
        self.assertEqual(stats["merges"], 0)
        self.assertEqual(sum(1 for i in trace.prog.instrs if i.op == "add"), 3)
        out = interp.run(trace.prog, {"x": 7})
        self.assertEqual(out[trace.value(trace.snapshots[-1].point, "o").name], 21)

    def test_input_dependent_branch_merges(self):
        mod = compile_body(self.tmp / "merge", """
            #include <stdint.h>
            #include "c2mix.h"
            void c2mix_body(void) {
              uint32_t o = 0, x = 0;
              c2mix_register("o", &o, 1, sizeof o, 0);
              c2mix_register("x", &x, 1, sizeof x, 0);
              c2mix_input("x");
              if (x & 1u) o = x + 1u; else o = x + 2u;
              c2mix_done();
            }
            """, "merge")
        trace, stats = execute.execute(mod, "c2mix_body")
        self.assertEqual(stats["merges"], 1)
        self.assertTrue(any(i.op == "ite" for i in trace.prog.instrs))
        last = trace.snapshots[-1].point
        for x, want in ((4, 6), (5, 6)):
            out = interp.run(trace.prog, {"x": x})
            self.assertEqual(out[trace.value(last, "o").name], want)

    def test_cut_markers_become_snapshots(self):
        mod = compile_body(self.tmp / "cuts", """
            #include <stdint.h>
            #include "c2mix.h"
            void c2mix_body(void) {
              uint32_t o = 0, x = 0;
              c2mix_register("o", &o, 1, sizeof o, 0);
              c2mix_register("x", &x, 1, sizeof x, 0);
              c2mix_input("x");
              for (int i = 0; i < 2; i++) { o = o + x; c2mix_cut(1); }
              c2mix_done();
            }
            """, "cuts")
        trace, _ = execute.execute(mod, "c2mix_body")
        self.assertEqual([(p.tag, p.k) for p in trace.cuts()], [("1", 1), ("1", 2)])

    def test_signedness_follows_the_producing_operation(self):
        mod = compile_body(self.tmp / "signs", """
            #include <stdint.h>
            #include "c2mix.h"
            void c2mix_body(void) {
              int32_t o = 0; int16_t a = 0;
              c2mix_register("o", &o, 1, sizeof o, 1);
              c2mix_register("a", &a, 1, sizeof a, 1);
              c2mix_input("a");
              o = (int32_t)a >> 3;
              c2mix_done();
            }
            """, "signs")
        trace, _ = execute.execute(mod, "c2mix_body")
        shifts = [i for i in trace.prog.instrs if i.op == "ashr"]
        self.assertTrue(shifts and shifts[0].args[0].signed and shifts[0].result.signed)


class HarnessTest(unittest.TestCase):
    def test_return_value_argument_is_assigned_not_passed(self):
        t = dsl.Target("f", args={"a": dsl.In("int32_t"), "r": dsl.Out("int16_t")},
                       returns="r")
        objs = harness.objects(t)
        text = harness.generate(t, "f", objs, includes=["reduce.c"])
        self.assertIn("r = f(a);", text)
        self.assertIn('c2mix_register("r", &r, 1, sizeof r, 1);', text)
        self.assertIn("void c2mix_body(void) {", text)
        self.assertNotIn("int main", text)

    def test_arrays_are_passed_by_name_and_out_scalars_by_address(self):
        t = dsl.Target("g", args={"out": dsl.Out("uint64_t"),
                                  "arg": dsl.In(dsl.Array("uint64_t", 4))})
        text = harness.generate(t, "g", harness.objects(t))
        self.assertIn("g(&out, arg);", text)
        self.assertIn("uint64_t arg[4] = {0};", text)

    def test_signedness_is_read_off_the_type_name(self):
        self.assertTrue(harness.guess_signed("int16_t"))
        self.assertFalse(harness.guess_signed("uint64_t"))
        self.assertFalse(harness.guess_signed("fiat_p256_uint1"))


if __name__ == "__main__":
    unittest.main()
