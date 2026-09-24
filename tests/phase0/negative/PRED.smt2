(set-info :smt-lib-version 2.0)
(set-logic ALL)
; variable declaration
(declare-const a_0 (_ BitVec 16))
(declare-const b_0 (_ BitVec 16))
(declare-const c_1 (_ BitVec 1))
(declare-const r_1 (_ BitVec 16))
(declare-const s__a_0 Int)
(declare-const s__b_0 Int)
(declare-const s__r_1 Int)
; range precondition and program 
(assert (and (bvslt #xC000 a_0) (bvslt a_0 #x4000) (bvslt #xC000 b_0) (bvslt b_0 #x4000)))
(assert (= s__a_0 (- (bv2nat a_0) (* 65536 (bv2nat ((_ extract 15 15) a_0))))))
(assert (= s__b_0 (- (bv2nat b_0) (* 65536 (bv2nat ((_ extract 15 15) b_0))))))
(assert (= r_1 (bvadd a_0 b_0)))
(assert (= s__r_1 (- (bv2nat r_1) (* 65536 (bv2nat ((_ extract 15 15) r_1))))))
(assert (= c_1 ((_ extract 15 15) r_1)))
; algebraic precondition and program
(assert true)
(assert (eqP (PConst s__r_1) (PAdd (PConst s__a_0) (PConst s__b_0))))
(assert (eqP (PMul (PConst (bv2nat c_1)) (PConst (bv2nat c_1))) (PConst (bv2nat c_1))))
; postcondition
(assert (not (and (eqmodP2 (PMul (PConst s__r_1) (PPow (PVar "x") 3)) (PMul (PAdd (PConst s__a_0) (PConst s__b_0)) (PVar "x")) (PConst 3) (PAdd (PPow (PVar "x") 2) (PConst (- 1)))) (eqmodP3 (PConst s__r_1) (PAdd (PConst s__b_0) (PConst s__a_0)) (PConst 7) (PConst 11) (PConst 13)))))
; check
(check-sat)
(exit)
