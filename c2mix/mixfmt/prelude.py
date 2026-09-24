"""The Poly prelude that extend_z3 injects after the `(set-logic` line (F2).

Copied verbatim from extend_z3/src/smt2_frontend.cpp (`poly_prelude`);
tests/phase0/test_prelude.py checks that the copy still matches.
"""

POLY_PRELUDE = """
(declare-datatype Poly
  (par (T)
    ((PConst (const_c T))
     (PVar   (var_name String))
     (PNeg   (neg_p (Poly T)))
     (PAdd   (add_l (Poly T)) (add_r (Poly T)))
     (PSub   (sub_l (Poly T)) (sub_r (Poly T)))
     (PMul   (mul_l (Poly T)) (mul_r (Poly T)))
     (PPow   (pow_base (Poly T)) (pow_k Int)))))

(declare-fun eqP ((Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP1 ((Poly Int) (Poly Int) (Poly Int)) Bool)

; kept for future
(declare-fun eqmodP2 ((Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP3 ((Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
(declare-fun eqmodP4 ((Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int) (Poly Int)) Bool)
"""

POLY_CONSTRUCTORS = {"PConst": 1, "PVar": 1, "PNeg": 1, "PAdd": 2, "PSub": 2, "PMul": 2, "PPow": 2}
POLY_PREDICATES = {"eqP": 2, "eqmodP1": 3, "eqmodP2": 4, "eqmodP3": 5, "eqmodP4": 6}
# Only these have compiled handling in extend_z3 (spec §1.3); the others are declared only.
SUPPORTED_PREDICATES = {"eqP", "eqmodP1", "eqmodP2"}
