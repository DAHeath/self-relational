(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 ((Array Int Int) Int Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 ((Array Int Int) Int Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 ((Array Int Int) Int Int Int Int Int Int Int Int (Array Int Int) Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V2 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int))
   (=> (and (= V2 1) (= head_0 V2) (= POINT_0 (+ V2 2)) (= tail_0 head_0) (= i_0 0) (= HEAP_0 HEAP_1) (= POINT_0 POINT_1) (= head_0 head_1) (= i_0 i_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1) (= tail_0 tail_1) (= tmp_0 tmp_1)) (R0 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V10 Int) (V5 (Array Int Int)) (V6 Int) (V7 Int) (V8 (Array Int Int)) (V9 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int))
   (=> (and (R0 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 V5 V7 head_1 V10 n_1 s0_1 s1_1 V9 V6) (< V10 n_1) (= V8 (store V5 V9 V10)) (= tmp_1 V7) (= POINT_1 (+ V7 2)) (= HEAP_1 (store V8 (+ V9 1) tmp_1)) (= tail_1 tmp_1) (= i_1 (+ V10 1))) (R0 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V11 Int) (V12 Int) (V13 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int))
   (=> (and (R0 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 HEAP_1 POINT_1 head_1 V11 n_1 V12 V13 tail_1 tmp_1) (not (< V11 n_1)) (= i_1 0) (= s0_1 0) (= s1_1 0)) (R1 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V14 (Array Int Int)) (V15 Int) (V16 Int) (V17 (Array Int Int)) (V18 Int) (V19 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int))
   (=> (and (R1 V14 V16 head_0 V19 n_0 s0_0 s1_0 V18 V15 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1) (not (not (= head_1 tail_1))) (< V19 n_0) (= V17 (store V14 V18 V19)) (= tmp_0 V16) (= POINT_0 (+ V16 2)) (= HEAP_0 (store V17 (+ V18 1) tmp_0)) (= tail_0 tmp_0) (= i_0 (+ V19 1))) (R1 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V20 Int) (V21 Int) (V22 Int) (V23 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int))
   (=> (and (R1 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 HEAP_1 POINT_1 V22 V23 n_1 V20 V21 tail_1 tmp_1) (not (= V22 tail_1)) (= s0_1 (+ V20 V23)) (= s1_1 (+ V21 (select HEAP_1 V22))) (= head_1 (select HEAP_1 (+ V22 1))) (= i_1 (+ V23 1)) (not (< i_0 n_0))) (R1 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V24 Int) (V25 Int) (V26 Int) (V27 Int) (V28 (Array Int Int)) (V29 Int) (V30 Int) (V31 (Array Int Int)) (V32 Int) (V33 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int))
   (=> (and (R1 V28 V30 head_0 V33 n_0 s0_0 s1_0 V32 V29 HEAP_1 POINT_1 V26 V27 n_1 V24 V25 tail_1 tmp_1) (not (= V26 tail_1)) (= s0_1 (+ V24 V27)) (= s1_1 (+ V25 (select HEAP_1 V26))) (= head_1 (select HEAP_1 (+ V26 1))) (= i_1 (+ V27 1)) (< V33 n_0) (= V31 (store V28 V32 V33)) (= tmp_0 V30) (= POINT_0 (+ V30 2)) (= HEAP_0 (store V31 (+ V32 1) tmp_0)) (= tail_0 tmp_0) (= i_0 (+ V33 1))) (R1 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V34 Int) (V35 Int) (V36 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int))
   (=> (and (R1 HEAP_0 POINT_0 head_0 V34 n_0 V35 V36 tail_0 tmp_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1) (not (not (= head_1 tail_1))) (not (< V34 n_0)) (= i_0 0) (= s0_0 0) (= s1_0 0)) (R2 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V37 Int) (V38 Int) (V39 Int) (V40 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int))
   (=> (and (R2 HEAP_0 POINT_0 V39 V40 n_0 V37 V38 tail_0 tmp_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1) (not (= V39 tail_0)) (= s0_0 (+ V37 V40)) (= s1_0 (+ V38 (select HEAP_0 V39))) (= head_0 (select HEAP_0 (+ V39 1))) (= i_0 (+ V40 1))) (R2 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (head_0 Int) (head_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int) (tail_0 Int) (tail_1 Int) (tmp_0 Int) (tmp_1 Int))
   (=> (and (R2 HEAP_0 POINT_0 head_0 i_0 n_0 s0_0 s1_0 tail_0 tmp_0 HEAP_1 POINT_1 head_1 i_1 n_1 s0_1 s1_1 tail_1 tmp_1) (not (not (= head_0 tail_0))) (= HEAP_0 HEAP_1) (= POINT_0 POINT_1) (= head_0 head_1) (= i_0 i_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1) (= tail_0 tail_1) (= tmp_0 tmp_1) (not (= s0_0 s1_0))) false)))


(check-sat)
(get-model)

