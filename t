(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R3 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R4 (Int Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((i0_1 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_1 Int) (s1_1 Int))
   (R0 0 0 n_0 0 0 i0_1 i1_1 n_1 s0_1 s1_1)))

(assert (forall ((i0_0 Int) (i0_0_0 Int) (i0_1 Int) (i0_1_0 Int) (i1_0 Int) (i1_0_0 Int) (i1_1 Int) (i1_1_0 Int) (n_0 Int) (n_0_0 Int) (n_1 Int) (n_1_0 Int) (s0_0 Int) (s0_0_0 Int) (s0_1 Int) (s0_1_0 Int) (s1_0 Int) (s1_0_0 Int) (s1_1 Int) (s1_1_0 Int))
   (=> (and (R0 i0_0_0 i1_0_0 n_0_0 s0_0_0 s1_0_0 i0_1_0 i1_1_0 n_1_0 s0_1_0 s1_1_0) (< i0_0 n_0)) (R0 (+ i0_0 1) i1_0 n_0 (+ s0_0 i0_0) s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R0 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (>= i0_0 n_0)) (R1 i0_1 i1_1 n_1 s0_1 s1_1 0 0 n_0 0 0))))

(assert (forall ((i0_0 Int) (i0_0_1 Int) (i0_1 Int) (i0_1_1 Int) (i1_0 Int) (i1_0_1 Int) (i1_1 Int) (i1_1_1 Int) (n_0 Int) (n_0_1 Int) (n_1 Int) (n_1_1 Int) (s0_0 Int) (s0_0_1 Int) (s0_1 Int) (s0_1_1 Int) (s1_0 Int) (s1_0_1 Int) (s1_1 Int) (s1_1_1 Int))
   (=> (and (R1 i0_1_1 i1_1_1 n_1_1 s0_1_1 s1_1_1 i0_0_1 i1_0_1 n_0_1 s0_0_1 s1_0_1) (< i1_1 n_1)) (R2 i0_1 (+ i1_1 1) n_1 s0_1 (+ s1_1 i1_1) i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R1 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R2 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R2 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (< i0_0 n_0)) (R3 (+ i0_0 1) i1_0 n_0 (+ s0_0 i0_0) s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R2 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R3 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R3 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (R1 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R1 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (>= i0_0 n_0)) (R4 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_0_1 Int) (i0_1 Int) (i0_1_1 Int) (i1_0 Int) (i1_0_1 Int) (i1_1 Int) (i1_1_1 Int) (n_0 Int) (n_0_1 Int) (n_1 Int) (n_1_1 Int) (s0_0 Int) (s0_0_1 Int) (s0_1 Int) (s0_1_1 Int) (s1_0 Int) (s1_0_1 Int) (s1_1 Int) (s1_1_1 Int))
   (=> (and (R4 i0_1_1 i1_1_1 n_1_1 s0_1_1 s1_1_1 i0_0_1 i1_0_1 n_0_1 s0_0_1 s1_0_1) (< i1_1 n_1)) (R4 i0_1 (+ i1_1 1) n_1 s0_1 (+ s1_1 i1_1) i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R4 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (>= i1_0 n_0) (not (= s0_0 s1_0))) false)))


(check-sat)
(get-model)

