(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (= s0_0 0) (= s1_0 0) (= i0_0 0) (= i1_0 0) (= i0_0 i0_1) (= i1_0 i1_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1)) (R0 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((V4 Int) (V5 Int) (i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R0 i0_0 i1_0 n_0 s0_0 s1_0 V5 i1_1 n_1 V4 s1_1) (< V5 n_1) (= s0_1 (+ V4 V5)) (= i0_1 (+ V5 1))) (R0 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R0 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (not (< i0_1 n_1))) (R1 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((V6 Int) (V7 Int) (i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R1 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 V7 n_1 s0_1 V6) (not (< i0_0 n_0)) (< V7 n_1) (= s1_1 (+ V6 V6)) (= i1_1 (+ V7 1))) (R1 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((V8 Int) (V9 Int) (i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R1 V9 i1_0 n_0 V8 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (< V9 n_0) (= s0_0 (+ V8 V9)) (= i0_0 (+ V9 1)) (not (< i1_1 n_1))) (R1 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((V10 Int) (V11 Int) (V12 Int) (V13 Int) (i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R1 V11 i1_0 n_0 V10 s1_0 i0_1 V13 n_1 s0_1 V12) (< V11 n_0) (= s0_0 (+ V10 V11)) (= i0_0 (+ V11 1)) (< V13 n_1) (= s1_1 (+ V12 V12)) (= i1_1 (+ V13 1))) (R1 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R1 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (not (< i0_0 n_0)) (not (< i1_1 n_1))) (R2 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((V14 Int) (V15 Int) (i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R2 i0_0 V15 n_0 s0_0 V14 i0_1 i1_1 n_1 s0_1 s1_1) (< V15 n_0) (= s1_0 (+ V14 V14)) (= i1_0 (+ V15 1))) (R2 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R2 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (not (< i1_0 n_0)) (= i0_0 i0_1) (= i1_0 i1_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1) (not (= s0_0 s1_0))) false)))


(check-sat)
(get-model)

