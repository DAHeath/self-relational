(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R3 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R4 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R5 (Int Int Int Int Int Int Int Int) Bool)
(declare-fun R6 (Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((n Int) (s1 Int))
   (R0 0 n 0 s1 0 n 0 s1)))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (and (R0 0 n 0 s1 i n s0 s1) (< i n)) (R1 0 n 0 s1 (+ i 1) n (+ s0 i) s1))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (and (R0 0 n 0 s1 i n s0 s1) (>= i n)) (R1 0 n 0 s1 i n s0 s1))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (R1 0 n 0 s1 i n s0 s1) (R0 0 n 0 s1 i n s0 s1))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (and (R0 0 n 0 s1 i n s0 s1) (>= i n)) (R2 0 n 0 s1 5 n s0 0))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (and (R2 i n s0 s1 i n s0 s1) (< i n)) (R3 (+ i 1) n (+ s0 i) s1 i n s0 s1))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (and (R2 i n s0 s1 i n s0 s1) (>= i n)) (R3 i n s0 s1 i n s0 s1))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (and (R3 i n s0 s1 i n s0 s1) (< i n)) (R4 i n s0 s1 (+ i 1) n s0 (+ s1 i)))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (and (R3 i n s0 s1 i n s0 s1) (>= i n)) (R4 i n s0 s1 i n s0 s1))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (R4 i n s0 s1 i n s0 s1) (R2 i n s0 s1 i n s0 s1))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (and (R2 i n s0 s1 i n s0 s1) (>= i n)) (R5 5 n s0 0 i n s0 s1))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (and (R5 i n s0 s1 i n s0 s1) (< i n)) (R6 (+ i 1) n s0 (+ s1 i) i n s0 s1))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (and (R5 i n s0 s1 i n s0 s1) (>= i n)) (R6 i n s0 s1 i n s0 s1))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (R6 i n s0 s1 i n s0 s1) (R5 i n s0 s1 i n s0 s1))))

(assert (forall ((i Int) (n Int) (s0 Int) (s1 Int))
   (=> (and (R5 i n s0 s1 i n s0 s1) (>= i n) (not (= s0 s1))) false)))


(check-sat)
(get-model)

