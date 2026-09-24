#!/usr/bin/env python3
"""Regenerate the A0.3 negative corpus: tests/phase0/negative/<CODE>.smt2.

Each file is clean/minimal.smt2 with one edit that violates exactly one lint rule.
test_negative.py checks that (static rules without z3; PARSE with z3), and that
this script's output still matches the committed files.
"""
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = (HERE / "clean" / "minimal.smt2").read_text()

DECL_S_R = "(declare-const s__r_1 Int)\n"
GOAL_LINE = next(l for l in BASE.splitlines() if l.startswith("(assert (not"))

COMPACT_PRELUDE = """(declare-datatype Poly (par (T) ((PConst (const_c T)) (PVar (var_name String)) (PNeg (neg_p (Poly T))) (PAdd (add_l (Poly T)) (add_r (Poly T))) (PSub (sub_l (Poly T)) (sub_r (Poly T))) (PMul (mul_l (Poly T)) (mul_r (Poly T))) (PPow (pow_base (Poly T)) (pow_k Int)))))
(declare-fun eqP ((Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP1 ((Poly Int) (Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP2 ((Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP3 ((Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP4 ((Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
"""


def rep(old, new, count=1):
    def f(s):
        assert s.count(old) >= count, old
        return s.replace(old, new) if count == 0 else s.replace(old, new, count)
    return f


EDITS = {
    # M1: no set-logic at all (extend_z3 then prepends the prelude; z3 defaults to ALL)
    "SET-LOGIC": rep("(set-logic ALL)\n", ""),
    # M2: the file brings its own Poly datatype (identical to the prelude, so z3 is fine)
    "POLY-DECL": rep("; variable declaration\n", "; variable declaration\n" + COMPACT_PRELUDE),
    # M3: a Poly sort other than (Poly Int)
    "POLY-SORT": rep("(declare-const r_1 ", "(declare-const g_0 (Poly Real))\n(declare-const r_1 "),
    # M3: eqmodP3 is declared by the prelude but has no compiled handling
    "PRED": rep("(eqmodP1 (PConst s__r_1) (PAdd (PConst s__b_0) (PConst s__a_0)) (PConst 7))",
                "(eqmodP3 (PConst s__r_1) (PAdd (PConst s__b_0) (PConst s__a_0)) (PConst 7) (PConst 11) (PConst 13))"),
    # M4: PVar takes a String-sorted constant instead of a literal
    "PVAR": lambda s: rep(DECL_S_R, DECL_S_R + "(declare-const vx String)\n")(s).replace('(PVar "x")', "(PVar vx)"),
    # M4: indeterminate encoded as a 1-bit bit-vector
    "INDET-BV": lambda s: rep(DECL_S_R, DECL_S_R + "(declare-const x_0 (_ BitVec 1))\n")(s)
        .replace('(PVar "x")', "(PConst (bv2nat x_0))"),
    # M5: bv2int instead of the alias
    "BV2INT": rep("(assert (eqP (PConst s__r_1) (PAdd (PConst s__a_0)",
                  "(assert (eqP (PConst s__r_1) (PAdd (PConst (bv2int a_0))"),
    # M5: compound PConst argument
    "PCONST-ATOM": rep("(assert (eqP (PConst s__r_1) (PAdd (PConst s__a_0)",
                       "(assert (eqP (PConst s__r_1) (PAdd (PConst (+ s__a_0 0))"),
    # M6: two commands in the postcondition section
    "GOAL": rep(GOAL_LINE + "\n", GOAL_LINE + "\n(assert true)\n"),
    # M6: trivial goal (allowed, but always reported as a warning)
    "TRIVIAL-GOAL": rep(GOAL_LINE, "(assert (not (and true true)))"),
    # M7: '.' in a symbol (legal SMT-LIB, outside the c2mix charset)
    "SYMBOL": rep("r_1", "r.1", 0),
    # M8: (_ bvN w) literal
    "CONST-FORMAT": rep("(bvslt #xC000 a_0)", "(bvslt (_ bv49152 16) a_0)"),
    # M10: the range comment lost its trailing space
    "SECTIONS": rep("; range precondition and program \n", "; range precondition and program\n"),
    # consumer: a symbol used but not declared (z3 rejects this too)
    "DECL": rep("(declare-const c_1 (_ BitVec 1))\n", ""),
    # §7.3: declarations not sorted
    "DECL-ORDER": rep("(declare-const a_0 (_ BitVec 16))\n(declare-const b_0 (_ BitVec 16))\n",
                      "(declare-const b_0 (_ BitVec 16))\n(declare-const a_0 (_ BitVec 16))\n"),
    # §7.3: an extra comment
    "LAYOUT": rep("(assert true)\n", "(assert true)\n; note\n"),
    # §6.1: alias with the wrong modulus
    "ALIAS": rep("(= s__b_0 (- (bv2nat b_0) (* 65536", "(= s__b_0 (- (bv2nat b_0) (* 32768"),
    # z3: sort error that no static rule sees
    "PARSE": rep("(bvadd a_0 b_0)", "(bvadd a_0 s__b_0)"),
}


def generate() -> dict[str, str]:
    return {code: edit(BASE) for code, edit in EDITS.items()}


if __name__ == "__main__":
    out = HERE / "negative"
    out.mkdir(exist_ok=True)
    for code, text in generate().items():
        (out / f"{code}.smt2").write_text(text)
    print(f"wrote {len(EDITS)} files to {out}")
