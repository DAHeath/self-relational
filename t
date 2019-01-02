(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 ((Array Int Int) Int Int Int Int (Array Int Int) Int Int Int Int) Bool)
(declare-fun R1 ((Array Int Int) Int Int Int Int (Array Int Int) Int Int Int Int) Bool)
(declare-fun R2 ((Array Int Int) Int Int Int Int (Array Int Int) Int Int Int Int) Bool)

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V2 Int) (a_0 Int) (a_1 Int) (b_0 Int) (b_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (= V2 1) (= a_0 V2) (= POINT_0 (+ V2 1)) (= b_0 a_0) (= HEAP_0 HEAP_1) (= POINT_0 POINT_1) (= a_0 a_1) (= b_0 b_1) (= x_0 x_1)) (R0 HEAP_0 POINT_0 a_0 b_0 x_0 HEAP_1 POINT_1 a_1 b_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V4 Int) (V5 Int) (V6 (Array Int Int)) (V7 Int) (a_0 Int) (a_1 Int) (b_0 Int) (b_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R0 HEAP_0 POINT_0 a_0 b_0 x_0 V6 V5 a_1 V7 V4) (= x_1 V5) (= POINT_1 (+ V5 1)) (= HEAP_1 (store V6 V7 x_1)) (= b_1 x_1)) (R0 HEAP_0 POINT_0 a_0 b_0 x_0 HEAP_1 POINT_1 a_1 b_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V8 (Array Int Int)) (a_0 Int) (a_1 Int) (b_0 Int) (b_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R0 HEAP_0 POINT_0 a_0 b_0 x_0 V8 POINT_1 a_1 b_1 x_1) (= HEAP_1 (store V8 b_1 0))) (R1 HEAP_0 POINT_0 a_0 b_0 x_0 HEAP_1 POINT_1 a_1 b_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V10 Int) (V11 (Array Int Int)) (V12 Int) (V9 Int) (a_0 Int) (a_1 Int) (b_0 Int) (b_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R1 V11 V10 a_0 V12 V9 HEAP_1 POINT_1 a_1 b_1 x_1) (not (not (= a_1 b_1))) (= x_0 V10) (= POINT_0 (+ V10 1)) (= HEAP_0 (store V11 V12 x_0)) (= b_0 x_0)) (R1 HEAP_0 POINT_0 a_0 b_0 x_0 HEAP_1 POINT_1 a_1 b_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V13 Int) (a_0 Int) (a_1 Int) (b_0 Int) (b_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R1 HEAP_0 POINT_0 a_0 b_0 x_0 HEAP_1 POINT_1 V13 b_1 x_1) (not (= V13 b_1)) (= a_1 (select HEAP_1 V13))) (R1 HEAP_0 POINT_0 a_0 b_0 x_0 HEAP_1 POINT_1 a_1 b_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V14 Int) (V15 Int) (V16 Int) (V17 (Array Int Int)) (V18 Int) (a_0 Int) (a_1 Int) (b_0 Int) (b_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R1 V17 V16 a_0 V18 V15 HEAP_1 POINT_1 V14 b_1 x_1) (not (= V14 b_1)) (= a_1 (select HEAP_1 V14)) (= x_0 V16) (= POINT_0 (+ V16 1)) (= HEAP_0 (store V17 V18 x_0)) (= b_0 x_0)) (R1 HEAP_0 POINT_0 a_0 b_0 x_0 HEAP_1 POINT_1 a_1 b_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V19 (Array Int Int)) (a_0 Int) (a_1 Int) (b_0 Int) (b_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R1 V19 POINT_0 a_0 b_0 x_0 HEAP_1 POINT_1 a_1 b_1 x_1) (not (not (= a_1 b_1))) (= HEAP_0 (store V19 b_0 0))) (R2 HEAP_0 POINT_0 a_0 b_0 x_0 HEAP_1 POINT_1 a_1 b_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (V20 Int) (a_0 Int) (a_1 Int) (b_0 Int) (b_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R2 HEAP_0 POINT_0 V20 b_0 x_0 HEAP_1 POINT_1 a_1 b_1 x_1) (not (= V20 b_0)) (= a_0 (select HEAP_0 V20))) (R2 HEAP_0 POINT_0 a_0 b_0 x_0 HEAP_1 POINT_1 a_1 b_1 x_1))))

(assert (forall ((HEAP_0 (Array Int Int)) (HEAP_1 (Array Int Int)) (POINT_0 Int) (POINT_1 Int) (a_0 Int) (a_1 Int) (b_0 Int) (b_1 Int) (x_0 Int) (x_1 Int))
   (=> (and (R2 HEAP_0 POINT_0 a_0 b_0 x_0 HEAP_1 POINT_1 a_1 b_1 x_1) (not (not (= a_0 b_0))) (= HEAP_0 HEAP_1) (= POINT_0 POINT_1) (= a_0 a_1) (= b_0 b_1) (= x_0 x_1) (not (= (select HEAP_0 a_0) 0))) false)))


(check-sat)
(get-model)

