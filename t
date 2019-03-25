(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R3 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R4 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R5 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R6 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R7 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R8 (Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R9 (Int Int Int Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((n_0 Int))
   (R0 0 n_0 0 0)))

(assert (forall ((i_2 Int) (i_3 Int) (n_2 Int) (n_3 Int) (s0_2 Int) (s0_3 Int) (s1_2 Int) (s1_3 Int))
   (=> (and (R0 i_3 n_3 s0_3 s1_3) (R0 i_2 n_2 s0_2 s1_2)) (R3 i_3 n_3 s0_3 s1_3 i_2 n_2 s0_2 s1_2))))

(assert (forall ((i_1 Int) (i_4 Int) (n_1 Int) (n_4 Int) (s0_1 Int) (s0_4 Int) (s1_1 Int) (s1_4 Int))
   (=> (R3 i_1 n_1 s0_1 s1_1 i_4 n_4 s0_4 s1_4) (R1 i_1 n_1 s0_1 s1_1 i_4 n_4 s0_4 s1_4))))

(assert (forall ((i_1 Int) (i_5 Int) (n_1 Int) (n_5 Int) (s0_1 Int) (s0_5 Int) (s1_1 Int) (s1_5 Int))
   (=> (and (R1 i_1 n_1 s0_1 s1_1 i_5 n_5 s0_5 s1_5) (< i_5 n_5)) (R1 i_1 n_1 s0_1 s1_1 (+ i_5 1) n_5 (+ s0_5 i_5) s1_5))))

(assert (forall ((i_1 Int) (i_6 Int) (n_1 Int) (n_6 Int) (s0_1 Int) (s0_6 Int) (s1_1 Int) (s1_6 Int))
   (=> (and (R1 i_1 n_1 s0_1 s1_1 i_6 n_6 s0_6 s1_6) (>= i_6 n_6)) (R1 i_1 n_1 s0_1 s1_1 i_6 n_6 s0_6 s1_6))))

(assert (forall ((i_7 Int) (i_8 Int) (n_7 Int) (n_8 Int) (s0_7 Int) (s0_8 Int) (s1_7 Int) (s1_8 Int))
   (=> (and (R1 i_7 n_7 s0_7 s1_7 i_8 n_8 s0_8 s1_8) (>= i_8 n_8)) (R4 i_7 n_7 s0_7 s1_7 1 n_8 s0_8 s1_8))))

(assert (forall ((i_10 Int) (i_9 Int) (n_10 Int) (n_9 Int) (s0_10 Int) (s0_9 Int) (s1_10 Int) (s1_9 Int))
   (=> (R4 i_9 n_9 s0_9 s1_9 i_10 n_10 s0_10 s1_10) (R5 i_9 n_9 s0_9 s1_9 i_10 n_10 s0_10 s1_10))))

(assert (forall ((i_12 Int) (i_13 Int) (n_12 Int) (n_13 Int) (s0_12 Int) (s0_13 Int) (s1_12 Int) (s1_13 Int))
   (=> (and (R5 i_13 n_13 s0_13 s1_13 i_12 n_12 s0_12 s1_12) (< i_13 n_13)) (R6 (+ i_13 1) n_13 (+ s0_13 i_13) s1_13 i_12 n_12 s0_12 s1_12))))

(assert (forall ((i_12 Int) (i_14 Int) (n_12 Int) (n_14 Int) (s0_12 Int) (s0_14 Int) (s1_12 Int) (s1_14 Int))
   (=> (and (R5 i_14 n_14 s0_14 s1_14 i_12 n_12 s0_12 s1_12) (>= i_14 n_14)) (R6 i_14 n_14 s0_14 s1_14 i_12 n_12 s0_12 s1_12))))

(assert (forall ((i_11 Int) (i_15 Int) (n_11 Int) (n_15 Int) (s0_11 Int) (s0_15 Int) (s1_11 Int) (s1_15 Int))
   (=> (and (R6 i_11 n_11 s0_11 s1_11 i_15 n_15 s0_15 s1_15) (< i_15 n_15)) (R5 i_11 n_11 s0_11 s1_11 (+ i_15 1) n_15 s0_15 (+ s1_15 i_15)))))

(assert (forall ((i_11 Int) (i_16 Int) (n_11 Int) (n_16 Int) (s0_11 Int) (s0_16 Int) (s1_11 Int) (s1_16 Int))
   (=> (and (R6 i_11 n_11 s0_11 s1_11 i_16 n_16 s0_16 s1_16) (>= i_16 n_16)) (R5 i_11 n_11 s0_11 s1_11 i_16 n_16 s0_16 s1_16))))

(assert (forall ((i_17 Int) (i_18 Int) (n_17 Int) (n_18 Int) (s0_17 Int) (s0_18 Int) (s1_17 Int) (s1_18 Int))
   (=> (and (R5 i_17 n_17 s0_17 s1_17 i_18 n_18 s0_18 s1_18) (>= i_18 n_18) (not (= s0_18 s1_18))) (R2 i_17 n_17 s0_17 s1_17 i_18 n_18 s0_18 s1_18))))

(assert (forall ((i_20 Int) (i_21 Int) (n_20 Int) (n_21 Int) (s0_20 Int) (s0_21 Int) (s1_20 Int) (s1_21 Int))
   (=> (and (R2 i_21 n_21 s0_21 s1_21 i_20 n_20 s0_20 s1_20) (>= i_21 n_21)) (R8 1 n_21 s0_21 s1_21 i_20 n_20 s0_20 s1_20 i_20 n_20 s0_20 s1_20))))

(assert (forall ((i_20 Int) (i_22 Int) (n_20 Int) (n_22 Int) (s0_20 Int) (s0_22 Int) (s1_20 Int) (s1_22 Int))
   (=> (R8 i_22 n_22 s0_22 s1_22 i_20 n_20 s0_20 s1_20 i_20 n_20 s0_20 s1_20) (R9 i_22 n_22 s0_22 s1_22 i_20 n_20 s0_20 s1_20 i_20 n_20 s0_20 s1_20))))

(assert (forall ((i_20 Int) (i_23 Int) (n_20 Int) (n_23 Int) (s0_20 Int) (s0_23 Int) (s1_20 Int) (s1_23 Int))
   (=> (and (R9 i_23 n_23 s0_23 s1_23 i_20 n_20 s0_20 s1_20 i_20 n_20 s0_20 s1_20) (< i_23 n_23)) (R9 (+ i_23 1) n_23 s0_23 (+ s1_23 i_23) i_20 n_20 s0_20 s1_20 i_20 n_20 s0_20 s1_20))))

(assert (forall ((i_20 Int) (i_24 Int) (n_20 Int) (n_24 Int) (s0_20 Int) (s0_24 Int) (s1_20 Int) (s1_24 Int))
   (=> (and (R9 i_24 n_24 s0_24 s1_24 i_20 n_20 s0_20 s1_20 i_20 n_20 s0_20 s1_20) (>= i_24 n_24)) (R9 i_24 n_24 s0_24 s1_24 i_20 n_20 s0_20 s1_20 i_20 n_20 s0_20 s1_20))))

(assert (forall ((i_20 Int) (i_25 Int) (n_20 Int) (n_25 Int) (s0_20 Int) (s0_25 Int) (s1_20 Int) (s1_25 Int))
   (=> (and (R9 i_25 n_25 s0_25 s1_25 i_20 n_20 s0_20 s1_20 i_20 n_20 s0_20 s1_20) (>= i_25 n_25) (not (= s0_25 s1_25))) (R7 i_25 n_25 s0_25 s1_25 i_20 n_20 s0_20 s1_20))))

(assert (forall ((i_19 Int) (i_26 Int) (n_19 Int) (n_26 Int) (s0_19 Int) (s0_26 Int) (s1_19 Int) (s1_26 Int))
   (=> (R7 i_19 n_19 s0_19 s1_19 i_26 n_26 s0_26 s1_26) false)))


(check-sat)
(get-model)

