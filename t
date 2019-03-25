(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R3 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R4 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R5 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R6 (Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((i_1 Int) (n_0 Int) (n_1 Int) (s0_1 Int) (s1_1 Int))
   (=> (and (= 0 i_1) (= n_0 n_1) (= 0 s0_1) (= 0 s1_1)) (R0 0 n_0 0 0 i_1 n_1 s0_1 s1_1))))

(assert (forall ((i_2 Int) (n_0 Int) (n_2 Int) (s0_2 Int) (s1_2 Int))
   (=> (and (R0 0 n_0 0 0 i_2 n_2 s0_2 s1_2) (< i_2 n_2)) (R1 0 n_0 0 0 (+ i_2 1) n_2 (+ s0_2 i_2) s1_2))))

(assert (forall ((i_2 Int) (n_0 Int) (n_2 Int) (s0_2 Int) (s1_2 Int))
   (=> (and (R0 0 n_0 0 0 i_2 n_2 s0_2 s1_2) (>= i_2 n_2)) (R1 0 n_0 0 0 i_2 n_2 s0_2 s1_2))))

(assert (forall ((i_3 Int) (n_0 Int) (n_3 Int) (s0_3 Int) (s1_3 Int))
   (=> (R1 0 n_0 0 0 i_3 n_3 s0_3 s1_3) (R0 0 n_0 0 0 i_3 n_3 s0_3 s1_3))))

(assert (forall ((i_2 Int) (n_0 Int) (n_2 Int) (s0_2 Int) (s1_2 Int))
   (=> (and (R0 0 n_0 0 0 i_2 n_2 s0_2 s1_2) (>= i_2 n_2)) (R2 0 n_0 0 0 0 n_2 s0_2 s1_2))))

(assert (forall ((i_4 Int) (i_5 Int) (n_4 Int) (n_5 Int) (s0_4 Int) (s0_5 Int) (s1_4 Int) (s1_5 Int))
   (=> (and (R2 i_4 n_4 s0_4 s1_4 i_5 n_5 s0_5 s1_5) (< i_4 n_4)) (R3 (+ i_4 1) n_4 (+ s0_4 i_4) s1_4 i_5 n_5 s0_5 s1_5))))

(assert (forall ((i_4 Int) (i_5 Int) (n_4 Int) (n_5 Int) (s0_4 Int) (s0_5 Int) (s1_4 Int) (s1_5 Int))
   (=> (and (R2 i_4 n_4 s0_4 s1_4 i_5 n_5 s0_5 s1_5) (>= i_4 n_4)) (R3 i_4 n_4 s0_4 s1_4 i_5 n_5 s0_5 s1_5))))

(assert (forall ((i_5 Int) (i_6 Int) (n_5 Int) (n_6 Int) (s0_5 Int) (s0_6 Int) (s1_5 Int) (s1_6 Int))
   (=> (and (R3 i_6 n_6 s0_6 s1_6 i_5 n_5 s0_5 s1_5) (< i_5 n_5)) (R4 i_6 n_6 s0_6 s1_6 (+ i_5 1) n_5 s0_5 (+ s1_5 i_5)))))

(assert (forall ((i_5 Int) (i_6 Int) (n_5 Int) (n_6 Int) (s0_5 Int) (s0_6 Int) (s1_5 Int) (s1_6 Int))
   (=> (and (R3 i_6 n_6 s0_6 s1_6 i_5 n_5 s0_5 s1_5) (>= i_5 n_5)) (R4 i_6 n_6 s0_6 s1_6 i_5 n_5 s0_5 s1_5))))

(assert (forall ((i_6 Int) (i_7 Int) (n_6 Int) (n_7 Int) (s0_6 Int) (s0_7 Int) (s1_6 Int) (s1_7 Int))
   (=> (R4 i_6 n_6 s0_6 s1_6 i_7 n_7 s0_7 s1_7) (R2 i_6 n_6 s0_6 s1_6 i_7 n_7 s0_7 s1_7))))

(assert (forall ((i_4 Int) (i_5 Int) (n_4 Int) (n_5 Int) (s0_4 Int) (s0_5 Int) (s1_4 Int) (s1_5 Int))
   (=> (and (R2 i_4 n_4 s0_4 s1_4 i_5 n_5 s0_5 s1_5) (>= i_4 n_4)) (R5 0 n_4 s0_4 s1_4 i_5 n_5 s0_5 s1_5))))

(assert (forall ((i_5 Int) (i_8 Int) (n_5 Int) (n_8 Int) (s0_5 Int) (s0_8 Int) (s1_5 Int) (s1_8 Int))
   (=> (and (R5 i_8 n_8 s0_8 s1_8 i_5 n_5 s0_5 s1_5) (< i_8 n_8)) (R6 (+ i_8 1) n_8 s0_8 (+ s1_8 i_8) i_5 n_5 s0_5 s1_5))))

(assert (forall ((i_5 Int) (i_8 Int) (n_5 Int) (n_8 Int) (s0_5 Int) (s0_8 Int) (s1_5 Int) (s1_8 Int))
   (=> (and (R5 i_8 n_8 s0_8 s1_8 i_5 n_5 s0_5 s1_5) (>= i_8 n_8)) (R6 i_8 n_8 s0_8 s1_8 i_5 n_5 s0_5 s1_5))))

(assert (forall ((i_5 Int) (i_9 Int) (n_5 Int) (n_9 Int) (s0_5 Int) (s0_9 Int) (s1_5 Int) (s1_9 Int))
   (=> (R6 i_9 n_9 s0_9 s1_9 i_5 n_5 s0_5 s1_5) (R5 i_9 n_9 s0_9 s1_9 i_5 n_5 s0_5 s1_5))))

(assert (forall ((i_5 Int) (i_8 Int) (n_5 Int) (n_8 Int) (s0_5 Int) (s0_8 Int) (s1_5 Int) (s1_8 Int))
   (=> (and (R5 i_8 n_8 s0_8 s1_8 i_5 n_5 s0_5 s1_5) (= i_8 i_5) (= n_8 n_5) (= s0_8 s0_5) (= s1_8 s1_5) (>= i_8 n_8) (not (= s0_8 s1_8))) false)))


(check-sat)
(get-model)

