(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((i0_6 Int) (i0_7 Int) (i1_1 Int) (i1_8 Int) (n_2 Int) (n_9 Int) (s0_10 Int) (s0_5 Int) (s1_11 Int) (s1_4 Int))
   (=> (and (= s0_5 0) (= i0_6 0)) (R0 i0_6 i1_1 n_2 s0_5 s1_4 i0_7 i1_8 n_9 s0_10 s1_11))))

(assert (forall ((i0_18 Int) (i0_6 Int) (i0_7 Int) (i1_1 Int) (i1_8 Int) (n_2 Int) (n_9 Int) (s0_10 Int) (s0_17 Int) (s0_5 Int) (s1_11 Int) (s1_4 Int))
   (=> (and (R0 i0_6 i1_1 n_2 s0_5 s1_4 i0_7 i1_8 n_9 s0_10 s1_11) (or (and (< i0_6 n_2) (= s0_17 (+ s0_5 i0_6)) (= i0_18 (+ i0_6 1))) (and (not (< i0_6 n_2)) (= i0_18 i0_6) (= s0_17 s0_5)))) (R0 i0_18 i1_1 n_2 s0_17 s1_4 i0_7 i1_8 n_9 s0_10 s1_11))))

(assert (forall ((i0_18 Int) (i0_6 Int) (i0_7 Int) (i1_1 Int) (i1_20 Int) (i1_8 Int) (n_2 Int) (n_9 Int) (s0_10 Int) (s0_17 Int) (s0_5 Int) (s1_11 Int) (s1_19 Int) (s1_4 Int))
   (=> (and (= s0_5 0) (= i0_6 0) (R0 i0_18 i1_1 n_2 s0_17 s1_4 i0_7 i1_8 n_9 s0_10 s1_11) (not (< i0_18 n_2)) (= s1_19 0) (= i1_20 0)) (R1 i0_18 i1_20 n_2 s0_17 s1_19 i0_6 i1_1 n_2 s0_5 s1_4))))

(assert (forall ((i0_18 Int) (i0_24 Int) (i0_6 Int) (i1_1 Int) (i1_20 Int) (i1_22 Int) (n_2 Int) (s0_17 Int) (s0_23 Int) (s0_5 Int) (s1_19 Int) (s1_21 Int) (s1_4 Int))
   (=> (and (R1 i0_18 i1_20 n_2 s0_17 s1_19 i0_6 i1_1 n_2 s0_5 s1_4) (or (and (< i1_20 n_2) (= s1_21 (+ s1_19 i1_20)) (= i1_22 (+ i1_20 1))) (and (not (< i1_20 n_2)) (= i1_22 i1_20) (= s1_21 s1_19))) (or (and (< i0_6 n_2) (= s0_23 (+ s0_5 i0_6)) (= i0_24 (+ i0_6 1))) (and (not (< i0_6 n_2)) (= i0_24 i0_6) (= s0_23 s0_5)))) (R1 i0_18 i1_22 n_2 s0_17 s1_21 i0_24 i1_1 n_2 s0_23 s1_4))))

(assert (forall ((i0_18 Int) (i0_24 Int) (i0_32 Int) (i1_1 Int) (i1_22 Int) (i1_26 Int) (i1_33 Int) (n_2 Int) (n_34 Int) (s0_17 Int) (s0_23 Int) (s0_35 Int) (s1_21 Int) (s1_25 Int) (s1_36 Int) (s1_4 Int))
   (=> (and (R1 i0_18 i1_22 n_2 s0_17 s1_21 i0_24 i1_1 n_2 s0_23 s1_4) (not (< i0_24 n_2)) (= s1_25 0) (= i1_26 0)) (R2 i0_24 i1_26 n_2 s0_23 s1_25 i0_32 i1_33 n_34 s0_35 s1_36))))

(assert (forall ((i0_24 Int) (i0_32 Int) (i1_26 Int) (i1_33 Int) (i1_38 Int) (n_2 Int) (n_34 Int) (s0_23 Int) (s0_35 Int) (s1_25 Int) (s1_36 Int) (s1_37 Int))
   (=> (and (R2 i0_24 i1_26 n_2 s0_23 s1_25 i0_32 i1_33 n_34 s0_35 s1_36) (or (and (< i1_26 n_2) (= s1_37 (+ s1_25 i1_26)) (= i1_38 (+ i1_26 1))) (and (not (< i1_26 n_2)) (= i1_38 i1_26) (= s1_37 s1_25)))) (R2 i0_24 i1_38 n_2 s0_23 s1_37 i0_32 i1_33 n_34 s0_35 s1_36))))

(assert (forall ((i0_18 Int) (i0_24 Int) (i0_32 Int) (i1_1 Int) (i1_22 Int) (i1_26 Int) (i1_33 Int) (i1_38 Int) (n_2 Int) (n_34 Int) (s0_17 Int) (s0_23 Int) (s0_35 Int) (s1_21 Int) (s1_25 Int) (s1_36 Int) (s1_37 Int) (s1_4 Int))
   (=> (and (R2 i0_24 i1_38 n_2 s0_23 s1_37 i0_32 i1_33 n_34 s0_35 s1_36) (R1 i0_18 i1_22 n_2 s0_17 s1_21 i0_24 i1_1 n_2 s0_23 s1_4) (not (< i0_24 n_2)) (= s1_25 0) (= i1_26 0) (= i0_24 i0_18) (= i1_38 i1_22) (= s0_23 s0_17) (= s1_37 s1_21) (not (< i1_38 n_2)) (not (= s0_23 s1_37))) false)))


(check-sat)
(get-model)

