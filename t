(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R3 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R4 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R5 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R6 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R7 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R8 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R9 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R10 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R11 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R12 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R13 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R14 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R15 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R16 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R17 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (and (= s0_0 0) (= s1_0 0) (= i0_0 0) (= i1_0 0) (= i0_0 i0_1) (= i1_0 i1_1) (= i2_0 i2_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1) (= s2_0 s2_1) (= s3_0 s3_1) (= i0_1 i0_2) (= i1_1 i1_2) (= i2_1 i2_2) (= n_1 n_2) (= s0_1 s0_2) (= s1_1 s1_2) (= s2_1 s2_2) (= s3_1 s3_2)) (R0 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((V4 Int) (V5 Int) (i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (and (R0 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 V5 i1_2 i2_2 n_2 V4 s1_2 s2_2 s3_2) (< V5 n_2) (= s0_2 (+ V4 V5)) (= i0_2 (+ V5 1))) (R1 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (and (R0 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (>= i0_2 n_2)) (R1 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (R1 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (R0 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (and (R0 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (>= i0_2 n_2)) (R2 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((V6 Int) (V7 Int) (i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (and (R2 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 V7 i2_2 n_2 s0_2 V6 s2_2 s3_2) (< V7 n_2) (= s1_2 (+ V6 V7)) (= i1_2 (+ V7 1))) (R3 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (and (R2 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (>= i1_2 n_2)) (R3 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((V8 Int) (V9 Int) (i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (and (R3 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 V9 i1_1 i2_1 n_1 V8 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (< V9 n_1) (= s0_1 (+ V8 V9)) (= i0_1 (+ V9 1))) (R4 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (and (R3 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (>= i0_1 n_1)) (R4 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (R4 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (R2 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (and (R2 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (>= i0_1 n_1)) (R5 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((V10 Int) (V11 Int) (i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (and (R5 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 V11 i2_1 n_1 s0_1 V10 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (< V11 n_1) (= s1_1 (+ V10 V11)) (= i1_1 (+ V11 1))) (R6 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (and (R5 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (>= i1_1 n_1)) (R6 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_2 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (n_0 Int) (n_1 Int) (n_2 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int))
   (=> (R6 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (R5 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2))))

(assert (forall ((V12 Int) (V13 Int) (V14 Int) (i0_0 Int) (i0_1 Int) (i0_2 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_2 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_2 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_2 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_2 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_2 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_2 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_2 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R5 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 V14 n_1 s0_1 s1_1 V12 V13 i0_2 i1_2 i2_2 n_2 s0_2 s1_2 s2_2 s3_2) (= i0_1 i0_2) (= i1_1 i1_2) (= V14 i2_2) (= n_1 n_2) (= s0_1 s0_2) (= s1_1 s1_2) (= V12 s2_2) (= V13 s3_2) (>= i1_1 n_1) (= s2_1 0) (= s3_1 0) (= i2_1 0) (= i0_1 i0_3) (= i1_1 i1_3) (= i2_1 i2_3) (= n_1 n_3) (= s0_1 s0_3) (= s1_1 s1_3) (= s2_1 s2_3) (= s3_1 s3_3) (= i0_0 i0_4) (= i1_0 i1_4) (= i2_0 i2_4) (= n_0 n_4) (= s0_0 s0_4) (= s1_0 s1_4) (= s2_0 s2_4) (= s3_0 s3_4)) (R7 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((V15 Int) (V16 Int) (V17 Int) (i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R7 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 V17 n_3 s0_3 s1_3 V15 V16 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (< V17 n_3) (= s2_3 (+ V15 V17)) (= s3_3 (+ V16 V17)) (= i2_3 (+ V17 1))) (R8 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R7 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (>= i2_3 n_3)) (R8 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((V18 Int) (V19 Int) (i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R8 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 V19 i1_4 i2_4 n_4 V18 s1_4 s2_4 s3_4) (< V19 n_4) (= s0_4 (+ V18 V19)) (= i0_4 (+ V19 1))) (R9 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R8 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (>= i0_4 n_4)) (R9 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (R9 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (R7 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R7 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (>= i0_4 n_4)) (R10 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((V20 Int) (V21 Int) (i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R10 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 V21 i2_4 n_4 s0_4 V20 s2_4 s3_4) (< V21 n_4) (= s1_4 (+ V20 V21)) (= i1_4 (+ V21 1))) (R11 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R10 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (>= i1_4 n_4)) (R11 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((V22 Int) (V23 Int) (V24 Int) (i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R11 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 V24 n_1 s0_1 s1_1 V22 V23 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (< V24 n_1) (= s2_1 (+ V22 V24)) (= s3_1 (+ V23 V24)) (= i2_1 (+ V24 1))) (R12 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R11 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (>= i2_1 n_1)) (R12 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((V25 Int) (V26 Int) (i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R12 V26 i1_0 i2_0 n_0 V25 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (< V26 n_0) (= s0_0 (+ V25 V26)) (= i0_0 (+ V26 1))) (R13 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R12 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (>= i0_0 n_0)) (R13 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (R13 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (R10 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R10 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (>= i0_0 n_0)) (R14 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((V27 Int) (V28 Int) (i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R14 i0_0 V28 i2_0 n_0 s0_0 V27 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (< V28 n_0) (= s1_0 (+ V27 V28)) (= i1_0 (+ V28 1))) (R15 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R14 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (>= i1_0 n_0)) (R15 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (R15 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (R14 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4))))

(assert (forall ((V29 Int) (V30 Int) (V31 Int) (i0_0 Int) (i0_1 Int) (i0_3 Int) (i0_4 Int) (i1_0 Int) (i1_1 Int) (i1_3 Int) (i1_4 Int) (i2_0 Int) (i2_1 Int) (i2_3 Int) (i2_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int) (s0_0 Int) (s0_1 Int) (s0_3 Int) (s0_4 Int) (s1_0 Int) (s1_1 Int) (s1_3 Int) (s1_4 Int) (s2_0 Int) (s2_1 Int) (s2_3 Int) (s2_4 Int) (s3_0 Int) (s3_1 Int) (s3_3 Int) (s3_4 Int))
   (=> (and (R14 i0_0 i1_0 V31 n_0 s0_0 s1_0 V29 V30 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1 i0_3 i1_3 i2_3 n_3 s0_3 s1_3 s2_3 s3_3 i0_4 i1_4 i2_4 n_4 s0_4 s1_4 s2_4 s3_4) (= i0_1 i0_3) (= i1_1 i1_3) (= i2_1 i2_3) (= n_1 n_3) (= s0_1 s0_3) (= s1_1 s1_3) (= s2_1 s2_3) (= s3_1 s3_3) (= i0_0 i0_4) (= i1_0 i1_4) (= V31 i2_4) (= n_0 n_4) (= s0_0 s0_4) (= s1_0 s1_4) (= V29 s2_4) (= V30 s3_4) (>= i1_0 n_0) (= s2_0 0) (= s3_0 0) (= i2_0 0)) (R16 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1))))

(assert (forall ((V32 Int) (V33 Int) (V34 Int) (i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (i2_0 Int) (i2_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (s2_0 Int) (s2_1 Int) (s3_0 Int) (s3_1 Int))
   (=> (and (R16 i0_0 i1_0 V34 n_0 s0_0 s1_0 V32 V33 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1) (< V34 n_0) (= s2_0 (+ V32 V34)) (= s3_0 (+ V33 V34)) (= i2_0 (+ V34 1))) (R17 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (i2_0 Int) (i2_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (s2_0 Int) (s2_1 Int) (s3_0 Int) (s3_1 Int))
   (=> (and (R16 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1) (>= i2_0 n_0)) (R17 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (i2_0 Int) (i2_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (s2_0 Int) (s2_1 Int) (s3_0 Int) (s3_1 Int))
   (=> (R17 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1) (R16 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (i2_0 Int) (i2_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (s2_0 Int) (s2_1 Int) (s3_0 Int) (s3_1 Int))
   (=> (and (R16 i0_0 i1_0 i2_0 n_0 s0_0 s1_0 s2_0 s3_0 i0_1 i1_1 i2_1 n_1 s0_1 s1_1 s2_1 s3_1) (= i0_0 i0_1) (= i1_0 i1_1) (= i2_0 i2_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1) (= s2_0 s2_1) (= s3_0 s3_1) (>= i2_0 n_0) (not (and (= s0_0 s2_0) (= s1_0 s3_0)))) false)))


(check-sat)
(get-model)

