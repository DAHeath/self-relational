(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((i_5 Int) (n_1 Int) (s0_4 Int) (s1_3 Int))
   (=> (and (= s0_4 0) (= i_5 0)) (R0 i_5 n_1 s0_4 s1_3 i_5 n_1 s0_4 s1_3))))

(assert (forall ((i_15 Int) (i_5 Int) (n_1 Int) (s0_14 Int) (s0_4 Int) (s1_3 Int))
   (=> (and (R0 i_5 n_1 s0_4 s1_3 i_5 n_1 s0_4 s1_3) (or (and (< i_5 n_1) (= s0_14 (+ s0_4 i_5)) (= i_15 (+ i_5 1))) (and (>= i_5 n_1) (= i_15 i_5) (= s0_14 s0_4)))) (R0 i_5 n_1 s0_4 s1_3 i_15 n_1 s0_14 s1_3))))

(assert (forall ((i_15 Int) (i_17 Int) (i_5 Int) (n_1 Int) (s0_14 Int) (s0_4 Int) (s1_16 Int) (s1_3 Int))
   (=> (and (R0 i_5 n_1 s0_4 s1_3 i_15 n_1 s0_14 s1_3) (>= i_15 n_1) (= s1_16 0) (= i_17 0)) (R1 i_5 n_1 s0_4 s1_3 i_17 n_1 s0_14 s1_16))))

(assert (forall ((i_17 Int) (i_19 Int) (i_21 Int) (i_5 Int) (n_1 Int) (s0_14 Int) (s0_18 Int) (s0_4 Int) (s1_16 Int) (s1_20 Int) (s1_3 Int))
   (=> (and (R1 i_5 n_1 s0_4 s1_3 i_17 n_1 s0_14 s1_16) (or (and (< i_5 n_1) (= s0_18 (+ s0_4 i_5)) (= i_19 (+ i_5 1))) (and (>= i_5 n_1) (= i_19 i_5) (= s0_18 s0_4))) (or (and (< i_17 n_1) (= s1_20 (+ s1_16 i_17)) (= i_21 (+ i_17 1))) (and (>= i_17 n_1) (= i_21 i_17) (= s1_20 s1_16)))) (R1 i_19 n_1 s0_18 s1_3 i_21 n_1 s0_14 s1_20))))

(assert (forall ((i_19 Int) (i_21 Int) (i_23 Int) (n_1 Int) (s0_14 Int) (s0_18 Int) (s1_20 Int) (s1_22 Int) (s1_3 Int))
   (=> (and (R1 i_19 n_1 s0_18 s1_3 i_21 n_1 s0_14 s1_20) (>= i_19 n_1) (= s1_22 0) (= i_23 0)) (R2 i_23 n_1 s0_18 s1_22 i_21 n_1 s0_14 s1_20))))

(assert (forall ((i_21 Int) (i_23 Int) (i_33 Int) (n_1 Int) (s0_14 Int) (s0_18 Int) (s1_20 Int) (s1_22 Int) (s1_32 Int))
   (=> (and (R2 i_23 n_1 s0_18 s1_22 i_21 n_1 s0_14 s1_20) (or (and (< i_23 n_1) (= s1_32 (+ s1_22 i_23)) (= i_33 (+ i_23 1))) (and (>= i_23 n_1) (= i_33 i_23) (= s1_32 s1_22)))) (R2 i_33 n_1 s0_18 s1_32 i_21 n_1 s0_14 s1_20))))

(assert (forall ((i_21 Int) (i_33 Int) (n_1 Int) (s0_14 Int) (s0_18 Int) (s1_20 Int) (s1_32 Int))
   (=> (and (R2 i_33 n_1 s0_18 s1_32 i_21 n_1 s0_14 s1_20) (= i_33 i_21) (= s0_18 s0_14) (= s1_32 s1_20) (>= i_33 n_1) (not (= s0_18 s1_32))) false)))


(check-sat)
(get-model)

