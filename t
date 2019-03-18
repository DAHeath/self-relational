(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((i_5 Int) (n_1 Int) (s0_4 Int) (s1_3 Int))
   (=> (and (= s0_4 0) (= i_5 0)) (R0 i_5 n_1 s0_4 s1_3 i_5 n_1 s0_4 s1_3))))

(assert (forall ((i_15 Int) (i_5 Int) (n_1 Int) (s0_14 Int) (s0_4 Int) (s1_3 Int))
   (=> (and (R0 i_5 n_1 s0_4 s1_3 i_5 n_1 s0_4 s1_3) (or (and (< i_5 n_1) (= s0_14 (+ s0_4 i_5)) (= i_15 (+ i_5 1))) (and (>= i_5 n_1) (= i_15 i_5) (= s0_14 s0_4)))) (R0 i_15 n_1 s0_14 s1_3 i_5 n_1 s0_4 s1_3))))

(assert (forall ((i_15 Int) (i_5 Int) (n_1 Int) (s0_14 Int) (s0_4 Int) (s1_16 Int) (s1_17 Int) (s1_3 Int))
   (=> (and (= s0_4 0) (= i_5 0) (R0 i_15 n_1 s0_14 s1_3 i_5 n_1 s0_4 s1_3) (>= i_15 n_1) (= s1_16 -1) (= s1_17 (+ s1_16 1))) (R1 i_15 n_1 s0_14 s1_17 i_5 n_1 s0_4 s1_3))))

(assert (forall ((i_15 Int) (i_19 Int) (i_21 Int) (i_5 Int) (n_1 Int) (s0_14 Int) (s0_20 Int) (s0_4 Int) (s1_17 Int) (s1_18 Int) (s1_3 Int))
   (=> (and (R1 i_15 n_1 s0_14 s1_17 i_5 n_1 s0_4 s1_3) (or (and (< i_15 n_1) (= s1_18 (+ s1_17 i_15)) (= i_19 (+ i_15 1))) (and (>= i_15 n_1) (= i_19 i_15) (= s1_18 s1_17))) (or (and (< i_5 n_1) (= s0_20 (+ s0_4 i_5)) (= i_21 (+ i_5 1))) (and (>= i_5 n_1) (= i_21 i_5) (= s0_20 s0_4)))) (R1 i_19 n_1 s0_14 s1_18 i_21 n_1 s0_20 s1_3))))

(assert (forall ((i_19 Int) (i_21 Int) (n_1 Int) (s0_14 Int) (s0_20 Int) (s1_18 Int) (s1_22 Int) (s1_23 Int) (s1_3 Int))
   (=> (and (R1 i_19 n_1 s0_14 s1_18 i_21 n_1 s0_20 s1_3) (>= i_21 n_1) (= s1_22 -1) (= s1_23 (+ s1_22 1))) (R2 i_21 n_1 s0_20 s1_23 i_19 n_1 s0_14 s1_18))))

(assert (forall ((i_19 Int) (i_21 Int) (i_33 Int) (n_1 Int) (s0_14 Int) (s0_20 Int) (s1_18 Int) (s1_23 Int) (s1_32 Int))
   (=> (and (R2 i_21 n_1 s0_20 s1_23 i_19 n_1 s0_14 s1_18) (or (and (< i_21 n_1) (= s1_32 (+ s1_23 i_21)) (= i_33 (+ i_21 1))) (and (>= i_21 n_1) (= i_33 i_21) (= s1_32 s1_23)))) (R2 i_33 n_1 s0_20 s1_32 i_19 n_1 s0_14 s1_18))))

(assert (forall ((i_19 Int) (i_21 Int) (i_33 Int) (n_1 Int) (s0_14 Int) (s0_20 Int) (s1_18 Int) (s1_22 Int) (s1_23 Int) (s1_3 Int) (s1_32 Int))
   (=> (and (R2 i_33 n_1 s0_20 s1_32 i_19 n_1 s0_14 s1_18) (R1 i_19 n_1 s0_14 s1_18 i_21 n_1 s0_20 s1_3) (>= i_21 n_1) (= s1_22 -1) (= s1_23 (+ s1_22 1)) (= i_33 i_19) (= s0_20 s0_14) (= s1_32 s1_18) (>= i_33 n_1) (not (= s0_20 s1_32))) false)))


(check-sat)
(get-model)

