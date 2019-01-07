(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun path (Int Int) Bool)

; (define-fun R0 ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int) (i0_1 Int) (i1_1 Int) (n_1 Int) (s0_1 Int) (s1_1 Int)) Bool
;  (and
;   (= n_0 n_1)
;   (= i0_0 0)
;   (= s1_0 0)
;   (= s0_0 0)
;   (= s1_1 0)
;   (or (and (<= i0_1 n_1) (>= n_0 0)) (and (= i0_1 0) (< n_0 0)))))

; (define-fun R1 ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int) (i0_1 Int) (i1_1 Int) (n_1 Int) (s0_1 Int) (s1_1 Int)) Bool
;  (and
;   (= n_0 n_1)
;   (or (and (= i0_1 n_1) (>= n_1 0)) (and (= i0_1 0) (< n_1 0)))
;   (or (and (<= i0_0 n_0) (>= n_0 0)) (and (= i0_0 0) (< n_0 0)))
;   (and
;     (=> (= i0_0 i1_1) (= s0_0 s1_1))
;     (=> (= i0_0 (+ i1_1 1)) (= s0_0 (+ s1_1 i1_1))))))

; (define-fun R2 ((i0_0 Int) (i1_0 Int) (n_0 Int) (s0_0 Int) (s1_0 Int) (i0_1 Int) (i1_1 Int) (n_1 Int) (s0_1 Int) (s1_1 Int)) Bool
;  (and
;   (= n_0 n_1)
;   (or (and (= i0_1 n_1) (>= n_1 0)) (and (= i0_1 0) (< n_1 0)))
;   (or (and (= i0_0 n_0) (>= n_0 0)) (and (= i0_0 0) (< n_0 0)))
;   (or (and (<= i1_0 n_1) (>= n_1 0)) (and (= i1_0 0) (< n_1 0)))
;   (=> (= i0_0 i1_1) (= s0_0 s1_1))))

; (define-fun path ((a Int) (b Int)) Bool
;   (or (= a b) (= a (+ b 1))))

(assert (forall ((a Int) (b Int))
  (=>
    (or
      (= a b)
      (= a (+ b 1)))
    (path a b))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (= s0_0 0) (= s1_0 0) (= i0_0 0)  (= i0_0 i0_1) (= i1_0 i1_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1)) 
 (R0 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((V4 Int) (V5 Int) (i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R0 i0_0 i1_0 n_0 s0_0 s1_0 V5 i1_1 n_1 V4 s1_1) (< V5 n_1) (= s0_1 (+ V4 V5)) (= i0_1 (+ V5 1))) 
 (R0 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R0 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (>= i0_1 n_1) (= i1_1 0))
 (R1 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((V6 Int) (V7 Int) (V8 Int) (V9 Int) (i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
 (=>
  (or
   (and
    (R1 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 V7 n_1 s0_1 V6)
    (path i0_0 V7)
    (path i0_0 i1_1)
    (< V7 n_1) (= s1_1 (+ V6 V7)) (= i1_1 (+ V7 1)))
   (and
    (R1 V9 i1_0 n_0 V8 s1_0 i0_1 i1_1 n_1 s0_1 s1_1)
    (path V9 i1_1)
    (path i0_0 i1_1)
    (< V9 n_0) (= s0_0 (+ V8 V9)) (= i0_0 (+ V9 1))))
  (R1 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((V Int) (i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R1 i0_0 V n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (>= i0_0 n_0)
   (= i1_0 0)
   ) (R2 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((V10 Int) (V11 Int) (i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R2 i0_0 V11 n_0 s0_0 V10 i0_1 i1_1 n_1 s0_1 s1_1) (< V11 n_0) (= s1_0 (+ V10 V11)) (= i1_0 (+ V11 1))) 
 (R2 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1))))

(assert (forall ((i0_0 Int) (i0_1 Int) (i1_0 Int) (i1_1 Int) (n_0 Int) (n_1 Int) (s0_0 Int) (s0_1 Int) (s1_0 Int) (s1_1 Int))
   (=> (and (R2 i0_0 i1_0 n_0 s0_0 s1_0 i0_1 i1_1 n_1 s0_1 s1_1) (= i0_0 i0_1) (= i1_0 i1_1) (= n_0 n_1) (= s0_0 s0_1) (= s1_0 s1_1) (>= i1_0 n_0) (not (= s0_0 s1_1))) 
 false)))


(check-sat)
(get-model)
