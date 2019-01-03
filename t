(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 ((Array Int Int) Int Int Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 ((Array Int Int) Int Int Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 ((Array Int Int) Int Int Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V2 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (= V2 1) (= head_0 V2) (= POINT_0 (+ V2 2)) (= tail_0 head_0) (= s0_0 0) (= i_0 0) (= HEAP_0 HEAP_1) (= POINT_0 POINT_1) (= head_0 head_1) (= i_0 i_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1) (= tail_0 tail_1) (= tmp_0 tmp_1) (= x_0 x_1)) (R0 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V10 (Array Int Int)) (V11 (Array Int Int)) (V12 Int) (V13 Int) (V6 Int) (V7 Int) (V8 Int) (V9 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R0 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 V10 V9 head_1 V13 n_1 V7 s1_1 V12 V8 V6) (< V13 n_1) (= s0_1 (+ V7 x_1)) (= tmp_1 V9) (= POINT_1 (+ V9 2)) (= V11 (store V10 V12 x_1)) (= HEAP_1 (store V11 (+ V12 1) tmp_1)) (= tail_1 tmp_1) (= i_1 (+ V13 1))) (R0 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V14 Int) (V15 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R0 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 V15 n_1 s0_1 V14 tail_1 tmp_1 x_1) (not (< V15 n_1)) (= s1_1 0) (= i_1 0)) (R1 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V16 Int) (V17 Int) (V18 Int) (V19 Int) (V20 (Array Int Int)) (V21 (Array Int Int)) (V22 Int) (V23 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R1 V20 V19 head_0 V23 n_0 V17 s1_0 V22 V18 V16 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1) (not (< i_1 n_1)) (< V23 n_0) (= s0_0 (+ V17 x_0)) (= tmp_0 V19) (= POINT_0 (+ V19 2)) (= V21 (store V20 V22 x_0)) (= HEAP_0 (store V21 (+ V22 1) tmp_0)) (= tail_0 tmp_0) (= i_0 (+ V23 1))) (R1 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V24 Int) (V25 Int) (V26 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R1 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 HEAP_1 POINT_1 V25 V26 n_1 s0_1 V24 tail_1 tmp_1 x_1) (< V26 n_1) (= s1_1 (+ V24 (select HEAP_1 V25))) (= head_1 (select HEAP_1 (+ V25 1))) (= i_1 (+ V26 1)) (not (< i_0 n_0))) (R1 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V27 Int) (V28 Int) (V29 Int) (V30 Int) (V31 Int) (V32 Int) (V33 Int) (V34 (Array Int Int)) (V35 (Array Int Int)) (V36 Int) (V37 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R1 V34 V33 head_0 V37 n_0 V31 s1_0 V36 V32 V30 HEAP_1 POINT_1 V28 V29 n_1 s0_1 V27 tail_1 tmp_1 x_1) (< V29 n_1) (= s1_1 (+ V27 (select HEAP_1 V28))) (= head_1 (select HEAP_1 (+ V28 1))) (= i_1 (+ V29 1)) (< V37 n_0) (= s0_0 (+ V31 x_0)) (= tmp_0 V33) (= POINT_0 (+ V33 2)) (= V35 (store V34 V36 x_0)) (= HEAP_0 (store V35 (+ V36 1) tmp_0)) (= tail_0 tmp_0) (= i_0 (+ V37 1))) (R1 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V38 Int) (V39 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R1 HEAP_0 POINT_0 head_0 V39 n_0 s0_0 V38 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1) (not (< i_1 n_1)) (not (< V39 n_0)) (= s1_0 0) (= i_0 0)) (R2 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V40 Int) (V41 Int) (V42 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R2 HEAP_0 POINT_0 V41 V42 n_0 s0_0 V40 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1) (< V42 n_0) (= s1_0 (+ V40 (select HEAP_0 V41))) (= head_0 (select HEAP_0 (+ V41 1))) (= i_0 (+ V42 1))) (R2 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R2 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 x_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1 x_1) (not (< i_0 n_0)) (= HEAP_0 HEAP_1) (= POINT_0 POINT_1) (= head_0 head_1) (= i_0 i_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1) (= tail_0 tail_1) (= tmp_0 tmp_1) (= x_0 x_1) (not (= s0_0 s1_0))) false)))


(check-sat)
(get-model)

