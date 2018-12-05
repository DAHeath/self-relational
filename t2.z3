(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int) Bool)
(declare-fun R3 (Int Int Int Int Int) Bool)
(declare-fun R4 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R5 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R6 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R7 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R8 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R9 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R10 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R11 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R12 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R13 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R14 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R15 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R16 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R17 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R18 (Int Int Int Int Int) Bool)
(declare-fun R19 (Int Int Int Int Int) Bool)
(declare-fun R20 (Int Int Int Int Int) Bool)
(declare-fun R21 (Int Int Int Int Int) Bool)
(declare-fun R22 (Int Int Int Int Int) Bool)
(declare-fun R23 (Int Int Int Int Int) Bool)
(declare-fun R24 (Int Int Int Int Int) Bool)
(declare-fun R25 (Int Int Int Int Int) Bool)
(declare-fun R26 (Int Int Int Int Int) Bool)
(declare-fun R27 (Int Int Int Int Int) Bool)
(declare-fun R28 (Int Int Int Int Int) Bool)

(declare-const n Int)
(declare-const i0 Int)
(declare-const i1 Int)
(declare-const s0 Int)
(declare-const s1 Int)

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (and (= n_0 n)
            (= i0_0 i0)
            (= i1_0 i1)
            (= s0_0 s0)
            (= s1_0 s1))
            (R0 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R4 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (R8 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R8 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R11 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R11 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R10 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R10 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R9 i0_1 i1_1 n_1 s0_1 s1_1 0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R9 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R7 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R7 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R6 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (< i1_1 n_1) (R6 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0)) (R14 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R14 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (R13 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 (+ s1_1 i1_1)))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R13 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (R12 i0_1 (+ i1_1 1) n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R6 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R12 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (< i0_0 n_0) (R12 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0)) (R16 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R16 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R15 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 (+ s0_0 i0_0) s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R15 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R6 i0_1 i1_1 n_1 s0_1 s1_1 (+ i0_0 1) i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R12 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R6 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R6 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0) (R17 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (>= i0_0 n_0) (R17 i0_1 i1_1 n_1 s0_1 s1_1 i0_0 i1_0 n_0 s0_0 s1_0)) (R5 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (R0 i0_0 i1_0 n_0 s0_0 s1_0) (R23 i0_0 i1_0 n_0 0 s1_0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (R23 i0_0 i1_0 n_0 s0_0 s1_0) (R22 i0_0 i1_0 n_0 s0_0 0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (R22 i0_0 i1_0 n_0 s0_0 s1_0) (R21 0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (R21 i0_0 i1_0 n_0 s0_0 s1_0) (R20 i0_0 0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (R20 i0_0 i1_0 n_0 s0_0 s1_0) (R19 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (and (< i0_0 n_0) (R19 i0_0 i1_0 n_0 s0_0 s1_0)) (R25 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (R25 i0_0 i1_0 n_0 s0_0 s1_0) (R24 i0_0 i1_0 n_0 (+ s0_0 i0_0) s1_0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (R24 i0_0 i1_0 n_0 s0_0 s1_0) (R19 (+ i0_0 1) i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (and (>= i0_0 n_0) (R19 i0_0 i1_0 n_0 s0_0 s1_0)) (R4 i0_0 i1_0 n_0 s0_0 s1_0 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R0 i0_0 i1_0 n_0 s0_0 s1_0) (R18 i0_1 i1_1 n_1 s0_1 s1_1)) (R4 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (R5 i0_0 i1_0 n_0 s0_0 s1_0 i0_0 i1_0 n_0 s0_0 s1_0) (R3 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (and (< i1_0 n_0) (R3 i0_0 i1_0 n_0 s0_0 s1_0)) (R28 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (R28 i0_0 i1_0 n_0 s0_0 s1_0) (R27 i0_0 i1_0 n_0 s0_0 (+ s1_0 i1_0)))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (R27 i0_0 i1_0 n_0 s0_0 s1_0) (R3 i0_0 (+ i1_0 1) n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R5 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (R26 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (R5 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (R3 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (and (>= i1_0 n_0) (R3 i0_0 i1_0 n_0 s0_0 s1_0)) (R2 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (and (not (=> (= i0_0 i1_0) (= s0_0 s1_0))) (R2 i0_0 i1_0 n_0 s0_0 s1_0)) (R1 i0_0 i1_0 n_0 s0_0 s1_0))))

(assert (forall ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int))
   (=> (R1 i0_0 i1_0 n_0 s0_0 s1_0) false)))


(check-sat)
(get-model)

