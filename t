(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R3 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R4 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R5 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R6 (Int Int Int Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((i_8 Int) (n_1 Int) (s0_6 Int) (s1_7 Int) (s2_4 Int) (s3_5 Int))
   (=> (and (= s0_6 0) (= s1_7 0) (= i_8 0)) (R0 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_8 n_1 s0_6 s1_7 s2_4 s3_5))))

(assert (forall ((i_11 Int) (i_8 Int) (n_1 Int) (s0_6 Int) (s0_9 Int) (s1_10 Int) (s1_7 Int) (s2_4 Int) (s3_5 Int))
   (=> (and (R0 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_8 n_1 s0_6 s1_7 s2_4 s3_5) (or (and (< i_8 n_1) (= s0_9 (+ s0_6 i_8)) (= s1_10 (+ s1_7 i_8)) (= i_11 (+ i_8 1))) (and (>= i_8 n_1) (= i_11 i_8) (= s0_9 s0_6) (= s1_10 s1_7)))) (R0 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_11 n_1 s0_9 s1_10 s2_4 s3_5))))

(assert (forall ((i_11 Int) (i_12 Int) (i_8 Int) (n_1 Int) (s0_6 Int) (s0_9 Int) (s1_10 Int) (s1_7 Int) (s2_13 Int) (s2_4 Int) (s3_5 Int))
   (=> (and (= s0_6 0) (= s1_7 0) (= i_8 0) (R0 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_11 n_1 s0_9 s1_10 s2_4 s3_5) (>= i_11 n_1) (= i_12 0) (= s2_13 0)) (R1 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_12 n_1 s0_9 s1_10 s2_13 s3_5 i_8 n_1 s0_6 s1_7 s2_4 s3_5))))

(assert (forall ((i_12 Int) (i_15 Int) (i_18 Int) (i_8 Int) (n_1 Int) (s0_16 Int) (s0_6 Int) (s0_9 Int) (s1_10 Int) (s1_17 Int) (s1_7 Int) (s2_13 Int) (s2_14 Int) (s2_4 Int) (s3_5 Int))
   (=> (and (R1 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_12 n_1 s0_9 s1_10 s2_13 s3_5 i_8 n_1 s0_6 s1_7 s2_4 s3_5) (or (and (< i_12 n_1) (= s2_14 (+ s2_13 i_12)) (= i_15 (+ i_12 1))) (and (>= i_12 n_1) (= i_15 i_12) (= s2_14 s2_13))) (or (and (< i_8 n_1) (= s0_16 (+ s0_6 i_8)) (= s1_17 (+ s1_7 i_8)) (= i_18 (+ i_8 1))) (and (>= i_8 n_1) (= i_18 i_8) (= s0_16 s0_6) (= s1_17 s1_7)))) (R1 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5 i_18 n_1 s0_16 s1_17 s2_4 s3_5))))

(assert (forall ((i_15 Int) (i_18 Int) (i_19 Int) (i_8 Int) (n_1 Int) (s0_16 Int) (s0_6 Int) (s0_9 Int) (s1_10 Int) (s1_17 Int) (s1_7 Int) (s2_14 Int) (s2_20 Int) (s2_4 Int) (s3_5 Int))
   (=> (and (R1 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5 i_18 n_1 s0_16 s1_17 s2_4 s3_5) (>= i_18 n_1) (= i_19 0) (= s2_20 0)) (R2 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_19 n_1 s0_16 s1_17 s2_20 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5))))

(assert (forall ((i_15 Int) (i_19 Int) (i_22 Int) (i_8 Int) (n_1 Int) (s0_16 Int) (s0_6 Int) (s0_9 Int) (s1_10 Int) (s1_17 Int) (s1_7 Int) (s2_14 Int) (s2_20 Int) (s2_21 Int) (s2_4 Int) (s3_5 Int))
   (=> (and (R2 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_19 n_1 s0_16 s1_17 s2_20 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5) (or (and (< i_19 n_1) (= s2_21 (+ s2_20 i_19)) (= i_22 (+ i_19 1))) (and (>= i_19 n_1) (= i_22 i_19) (= s2_21 s2_20)))) (R2 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_22 n_1 s0_16 s1_17 s2_21 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5))))

(assert (forall ((i_15 Int) (i_18 Int) (i_19 Int) (i_22 Int) (i_23 Int) (i_8 Int) (n_1 Int) (s0_16 Int) (s0_6 Int) (s0_9 Int) (s1_10 Int) (s1_17 Int) (s1_7 Int) (s2_14 Int) (s2_20 Int) (s2_21 Int) (s2_4 Int) (s3_24 Int) (s3_5 Int))
   (=> (and (= s0_6 0) (= s1_7 0) (= i_8 0) (R2 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_22 n_1 s0_16 s1_17 s2_21 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5) (R1 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5 i_18 n_1 s0_16 s1_17 s2_4 s3_5) (>= i_18 n_1) (= i_19 0) (= s2_20 0) (= i_22 i_15) (= s0_16 s0_9) (= s1_17 s1_10) (= s2_21 s2_14) (>= i_22 n_1) (= i_23 0) (= s3_24 0)) (R3 i_23 n_1 s0_16 s1_17 s2_21 s3_24 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_23 n_1 s0_16 s1_17 s2_21 s3_24 i_8 n_1 s0_6 s1_7 s2_4 s3_5))))

(assert (forall ((i_23 Int) (i_26 Int) (i_29 Int) (i_8 Int) (n_1 Int) (s0_16 Int) (s0_27 Int) (s0_6 Int) (s1_17 Int) (s1_28 Int) (s1_7 Int) (s2_21 Int) (s2_4 Int) (s3_24 Int) (s3_25 Int) (s3_5 Int))
   (=> (and (R3 i_23 n_1 s0_16 s1_17 s2_21 s3_24 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_23 n_1 s0_16 s1_17 s2_21 s3_24 i_8 n_1 s0_6 s1_7 s2_4 s3_5) (or (and (< i_23 n_1) (= s3_25 (+ s3_24 i_23)) (= i_26 (+ i_23 1))) (and (>= i_23 n_1) (= i_26 i_23) (= s3_25 s3_24))) (or (and (< i_8 n_1) (= s0_27 (+ s0_6 i_8)) (= s1_28 (+ s1_7 i_8)) (= i_29 (+ i_8 1))) (and (>= i_8 n_1) (= i_29 i_8) (= s0_27 s0_6) (= s1_28 s1_7)))) (R3 i_23 n_1 s0_16 s1_17 s2_21 s3_24 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25 i_29 n_1 s0_27 s1_28 s2_4 s3_5))))

(assert (forall ((i_15 Int) (i_18 Int) (i_19 Int) (i_22 Int) (i_23 Int) (i_26 Int) (i_29 Int) (i_30 Int) (i_8 Int) (n_1 Int) (s0_16 Int) (s0_27 Int) (s0_6 Int) (s0_9 Int) (s1_10 Int) (s1_17 Int) (s1_28 Int) (s1_7 Int) (s2_14 Int) (s2_20 Int) (s2_21 Int) (s2_31 Int) (s2_4 Int) (s3_24 Int) (s3_25 Int) (s3_5 Int))
   (=> (and (= s0_6 0) (= s1_7 0) (= i_8 0) (R2 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_22 n_1 s0_16 s1_17 s2_21 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5) (R1 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5 i_18 n_1 s0_16 s1_17 s2_4 s3_5) (>= i_18 n_1) (= i_19 0) (= s2_20 0) (= i_22 i_15) (= s0_16 s0_9) (= s1_17 s1_10) (= s2_21 s2_14) (>= i_22 n_1) (= i_23 0) (= s3_24 0) (R3 i_23 n_1 s0_16 s1_17 s2_21 s3_24 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25 i_29 n_1 s0_27 s1_28 s2_4 s3_5) (>= i_29 n_1) (= i_30 0) (= s2_31 0)) (R4 i_30 n_1 s0_27 s1_28 s2_31 s3_5 i_23 n_1 s0_16 s1_17 s2_21 s3_24 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25))))

(assert (forall ((i_23 Int) (i_26 Int) (i_30 Int) (i_33 Int) (i_35 Int) (i_38 Int) (i_8 Int) (n_1 Int) (s0_16 Int) (s0_27 Int) (s0_36 Int) (s0_6 Int) (s1_17 Int) (s1_28 Int) (s1_37 Int) (s1_7 Int) (s2_21 Int) (s2_31 Int) (s2_32 Int) (s2_4 Int) (s3_24 Int) (s3_25 Int) (s3_34 Int) (s3_5 Int))
   (=> (and (R4 i_30 n_1 s0_27 s1_28 s2_31 s3_5 i_23 n_1 s0_16 s1_17 s2_21 s3_24 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25) (or (and (< i_30 n_1) (= s2_32 (+ s2_31 i_30)) (= i_33 (+ i_30 1))) (and (>= i_30 n_1) (= i_33 i_30) (= s2_32 s2_31))) (or (and (< i_23 n_1) (= s3_34 (+ s3_24 i_23)) (= i_35 (+ i_23 1))) (and (>= i_23 n_1) (= i_35 i_23) (= s3_34 s3_24))) (or (and (< i_8 n_1) (= s0_36 (+ s0_6 i_8)) (= s1_37 (+ s1_7 i_8)) (= i_38 (+ i_8 1))) (and (>= i_8 n_1) (= i_38 i_8) (= s0_36 s0_6) (= s1_37 s1_7)))) (R4 i_33 n_1 s0_27 s1_28 s2_32 s3_5 i_35 n_1 s0_16 s1_17 s2_21 s3_34 i_38 n_1 s0_36 s1_37 s2_4 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25))))

(assert (forall ((i_15 Int) (i_18 Int) (i_19 Int) (i_22 Int) (i_23 Int) (i_26 Int) (i_29 Int) (i_30 Int) (i_33 Int) (i_35 Int) (i_38 Int) (i_39 Int) (i_8 Int) (n_1 Int) (s0_16 Int) (s0_27 Int) (s0_36 Int) (s0_6 Int) (s0_9 Int) (s1_10 Int) (s1_17 Int) (s1_28 Int) (s1_37 Int) (s1_7 Int) (s2_14 Int) (s2_20 Int) (s2_21 Int) (s2_31 Int) (s2_32 Int) (s2_4 Int) (s2_40 Int) (s3_24 Int) (s3_25 Int) (s3_34 Int) (s3_5 Int))
   (=> (and (R4 i_33 n_1 s0_27 s1_28 s2_32 s3_5 i_35 n_1 s0_16 s1_17 s2_21 s3_34 i_38 n_1 s0_36 s1_37 s2_4 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25) (>= i_38 n_1) (= i_39 0) (= s2_40 0) (= s0_6 0) (= s1_7 0) (= i_8 0) (R2 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_22 n_1 s0_16 s1_17 s2_21 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5) (R1 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5 i_18 n_1 s0_16 s1_17 s2_4 s3_5) (>= i_18 n_1) (= i_19 0) (= s2_20 0) (= i_22 i_15) (= s0_16 s0_9) (= s1_17 s1_10) (= s2_21 s2_14) (>= i_22 n_1) (= i_23 0) (= s3_24 0) (R3 i_23 n_1 s0_16 s1_17 s2_21 s3_24 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25 i_29 n_1 s0_27 s1_28 s2_4 s3_5) (>= i_29 n_1) (= i_30 0) (= s2_31 0)) (R5 i_35 n_1 s0_16 s1_17 s2_21 s3_34 i_39 n_1 s0_36 s1_37 s2_40 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25 i_33 n_1 s0_27 s1_28 s2_32 s3_5))))

(assert (forall ((i_26 Int) (i_33 Int) (i_35 Int) (i_39 Int) (i_42 Int) (n_1 Int) (s0_16 Int) (s0_27 Int) (s0_36 Int) (s1_17 Int) (s1_28 Int) (s1_37 Int) (s2_21 Int) (s2_32 Int) (s2_40 Int) (s2_41 Int) (s3_25 Int) (s3_34 Int) (s3_5 Int))
   (=> (and (R5 i_35 n_1 s0_16 s1_17 s2_21 s3_34 i_39 n_1 s0_36 s1_37 s2_40 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25 i_33 n_1 s0_27 s1_28 s2_32 s3_5) (or (and (< i_39 n_1) (= s2_41 (+ s2_40 i_39)) (= i_42 (+ i_39 1))) (and (>= i_39 n_1) (= i_42 i_39) (= s2_41 s2_40)))) (R5 i_35 n_1 s0_16 s1_17 s2_21 s3_34 i_42 n_1 s0_36 s1_37 s2_41 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25 i_33 n_1 s0_27 s1_28 s2_32 s3_5))))

(assert (forall ((i_15 Int) (i_18 Int) (i_19 Int) (i_22 Int) (i_23 Int) (i_26 Int) (i_29 Int) (i_30 Int) (i_33 Int) (i_35 Int) (i_38 Int) (i_39 Int) (i_42 Int) (i_43 Int) (i_8 Int) (n_1 Int) (s0_16 Int) (s0_27 Int) (s0_36 Int) (s0_6 Int) (s0_9 Int) (s1_10 Int) (s1_17 Int) (s1_28 Int) (s1_37 Int) (s1_7 Int) (s2_14 Int) (s2_20 Int) (s2_21 Int) (s2_31 Int) (s2_32 Int) (s2_4 Int) (s2_40 Int) (s2_41 Int) (s3_24 Int) (s3_25 Int) (s3_34 Int) (s3_44 Int) (s3_5 Int))
   (=> (and (R4 i_33 n_1 s0_27 s1_28 s2_32 s3_5 i_35 n_1 s0_16 s1_17 s2_21 s3_34 i_38 n_1 s0_36 s1_37 s2_4 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25) (>= i_38 n_1) (= i_39 0) (= s2_40 0) (= s0_6 0) (= s1_7 0) (= i_8 0) (R2 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_22 n_1 s0_16 s1_17 s2_21 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5) (R1 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5 i_18 n_1 s0_16 s1_17 s2_4 s3_5) (>= i_18 n_1) (= i_19 0) (= s2_20 0) (= i_22 i_15) (= s0_16 s0_9) (= s1_17 s1_10) (= s2_21 s2_14) (>= i_22 n_1) (= i_23 0) (= s3_24 0) (R3 i_23 n_1 s0_16 s1_17 s2_21 s3_24 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25 i_29 n_1 s0_27 s1_28 s2_4 s3_5) (>= i_29 n_1) (= i_30 0) (= s2_31 0) (R5 i_35 n_1 s0_16 s1_17 s2_21 s3_34 i_42 n_1 s0_36 s1_37 s2_41 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25 i_33 n_1 s0_27 s1_28 s2_32 s3_5) (= i_35 i_26) (= s3_34 s3_25) (= i_42 i_33) (= s0_36 s0_27) (= s1_37 s1_28) (= s2_41 s2_32) (>= i_42 n_1) (= i_43 0) (= s3_44 0)) (R6 i_43 n_1 s0_36 s1_37 s2_41 s3_44 i_35 n_1 s0_16 s1_17 s2_21 s3_34))))

(assert (forall ((i_35 Int) (i_43 Int) (i_46 Int) (n_1 Int) (s0_16 Int) (s0_36 Int) (s1_17 Int) (s1_37 Int) (s2_21 Int) (s2_41 Int) (s3_34 Int) (s3_44 Int) (s3_45 Int))
   (=> (and (R6 i_43 n_1 s0_36 s1_37 s2_41 s3_44 i_35 n_1 s0_16 s1_17 s2_21 s3_34) (or (and (< i_43 n_1) (= s3_45 (+ s3_44 i_43)) (= i_46 (+ i_43 1))) (and (>= i_43 n_1) (= i_46 i_43) (= s3_45 s3_44)))) (R6 i_46 n_1 s0_36 s1_37 s2_41 s3_45 i_35 n_1 s0_16 s1_17 s2_21 s3_34))))

(assert (forall ((i_15 Int) (i_18 Int) (i_19 Int) (i_22 Int) (i_23 Int) (i_26 Int) (i_29 Int) (i_30 Int) (i_33 Int) (i_35 Int) (i_38 Int) (i_39 Int) (i_42 Int) (i_43 Int) (i_46 Int) (i_8 Int) (n_1 Int) (s0_16 Int) (s0_27 Int) (s0_36 Int) (s0_6 Int) (s0_9 Int) (s1_10 Int) (s1_17 Int) (s1_28 Int) (s1_37 Int) (s1_7 Int) (s2_14 Int) (s2_20 Int) (s2_21 Int) (s2_31 Int) (s2_32 Int) (s2_4 Int) (s2_40 Int) (s2_41 Int) (s3_24 Int) (s3_25 Int) (s3_34 Int) (s3_44 Int) (s3_45 Int) (s3_5 Int))
   (=> (and (R6 i_46 n_1 s0_36 s1_37 s2_41 s3_45 i_35 n_1 s0_16 s1_17 s2_21 s3_34) (R4 i_33 n_1 s0_27 s1_28 s2_32 s3_5 i_35 n_1 s0_16 s1_17 s2_21 s3_34 i_38 n_1 s0_36 s1_37 s2_4 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25) (>= i_38 n_1) (= i_39 0) (= s2_40 0) (= s0_6 0) (= s1_7 0) (= i_8 0) (R2 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_22 n_1 s0_16 s1_17 s2_21 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5) (R1 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_15 n_1 s0_9 s1_10 s2_14 s3_5 i_18 n_1 s0_16 s1_17 s2_4 s3_5) (>= i_18 n_1) (= i_19 0) (= s2_20 0) (= i_22 i_15) (= s0_16 s0_9) (= s1_17 s1_10) (= s2_21 s2_14) (>= i_22 n_1) (= i_23 0) (= s3_24 0) (R3 i_23 n_1 s0_16 s1_17 s2_21 s3_24 i_8 n_1 s0_6 s1_7 s2_4 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25 i_29 n_1 s0_27 s1_28 s2_4 s3_5) (>= i_29 n_1) (= i_30 0) (= s2_31 0) (R5 i_35 n_1 s0_16 s1_17 s2_21 s3_34 i_42 n_1 s0_36 s1_37 s2_41 s3_5 i_26 n_1 s0_16 s1_17 s2_21 s3_25 i_33 n_1 s0_27 s1_28 s2_32 s3_5) (= i_35 i_26) (= s3_34 s3_25) (= i_42 i_33) (= s0_36 s0_27) (= s1_37 s1_28) (= s2_41 s2_32) (>= i_42 n_1) (= i_43 0) (= s3_44 0) (= i_46 i_35) (= s0_36 s0_16) (= s1_37 s1_17) (= s2_41 s2_21) (= s3_45 s3_34) (>= i_46 n_1) (not (and (= s0_36 s2_41) (= s1_37 s3_45)))) false)))


(check-sat)
(get-model)

