(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (= s0_0 0) (= s1_0 0) (= i_0 0) (= i_0 i_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1)) (R0 i_0 n_0 s0_0 s1_0 i_1 n_1 s0_1 s1_1))))

(assert (forall ((V3 Int) (V4 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R0 i_0 n_0 s0_0 s1_0 V4 n_1 V3 s1_1) (< V4 n_1) (= s0_1 (+ V3 V4)) (= i_1 (+ V4 1))) (R0 i_0 n_0 s0_0 s1_0 i_1 n_1 s0_1 s1_1))))

(assert (forall ((V5 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R0 i_0 n_0 s0_0 s1_0 V5 n_1 s0_1 s1_1) (not (< V5 n_1)) (= i_1 0)) (R1 i_0 n_0 s0_0 s1_0 i_1 n_1 s0_1 s1_1))))

(assert (forall ((V10 Int) (V11 Int) (V12 Int) (V13 Int) (V6 Int) (V7 Int) (V8 Int) (V9 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (or 
(and (R1 V7 n_0 V6 s1_0 i_1 n_1 s0_1 s1_1) (not (< i_1 n_1)) (< V7 n_0) (= s0_0 (+ V6 V7)) (= i_0 (+ V7 1))) 
(and (R1 i_0 n_0 s0_0 s1_0 V9 n_1 s0_1 V8) (< V9 n_1) (= s1_1 (+ V8 V9)) (= i_1 (+ V9 1)) (not (< i_0 n_0))) 
(and (R1 V13 n_0 V12 s1_0 V11 n_1 s0_1 V10) (< V11 n_1) (= s1_1 (+ V10 V11)) (= i_1 (+ V11 1)) (< V13 n_0) (= s0_0 (+ V12 V13)) (= i_0 (+ V13 1)))) (R1 i_0 n_0 s0_0 s1_0 i_1 n_1 s0_1 s1_1))))

(assert (forall ((V14 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R1 V14 n_0 s0_0 s1_0 i_1 n_1 s0_1 s1_1) (not (< i_1 n_1)) (not (< V14 n_0)) (= i_0 0)) (R2 i_0 n_0 s0_0 s1_0 i_1 n_1 s0_1 s1_1))))

(assert (forall ((V15 Int) (V16 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R2 V16 n_0 s0_0 V15 i_1 n_1 s0_1 s1_1) (< V16 n_0) (= s1_0 (+ V15 V16)) (= i_0 (+ V16 1))) (R2 i_0 n_0 s0_0 s1_0 i_1 n_1 s0_1 s1_1))))

(assert (forall ((i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R2 i_0 n_0 s0_0 s1_0 i_1 n_1 s0_1 s1_1) (not (< i_0 n_0)) (= i_0 i_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1) (not (= s0_0 s1_0))) false)))


(check-sat)
(get-model)

