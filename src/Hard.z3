;; s0, s1, s2, s3 := 0
;; i := 0
;; while i < n {   R0
;;   i := i + 1
;;   s0 := s0 + 1
;; }
;; i := 0
;; while i < n {   R1
;;   i := i + 1
;;   s1 := s1 + 2
;; }
;; i := 0
;; while i < n {   R2
;;   i := i + 1
;;   s2 := s2 + 1
;;   s3 := s3 + 2
;; }
;; assert s0 = s2 /\ s1 = s3
(set-logic HORN)
(set-option :fixedpoint.engine duality)

(declare-fun R0 (Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int) Bool)
(declare-fun R ( Int Int Int Int Int
                 Int Int Int Int Int
                 Int Int Int Int Int
                 Int ) Bool)

;; partition
;; R0(0, 0, 0, 0, 0, n)
(assert (forall ((n Int)) (=> (> n 0) (R0 0 0 0 0 0 n))))

;; loop invariant
;; R0(s0 + 1, s1, s2, s3, i + 1, n) /\ i < n => R0(s0, s1, s2, s3, i, n)
(assert (forall ((s0 Int) (s1 Int) (s2 Int) (s3 Int) (i Int) (n Int))
  (=> (and (R0 s0 s1 s2 s3 i n) (< i n))
      (R0 (+ s0 1) s1 s2 s3 (+ i 1) n))))

;; progress
;; R0(s0, s1, s2, s3, i, n) /\ i >= n => R1(s0, s1, s2, s3, 0, n)
(assert (forall ((s0 Int) (s1 Int) (s2 Int) (s3 Int) (i Int) (n Int))
  (=> (and (R0 s0 s1 s2 s3 i n) (>= i n))
      (R1 s0 s1 s2 s3 0 n))))

;; loop invariant
;; R1(s0, s1 + 2, s2, s3, i + 1, n) /\ i < n => R1(s0, s1, s2, s3, i, n)
(assert (forall ((s0 Int) (s1 Int) (s2 Int) (s3 Int) (i Int) (n Int))
  (=> (and (R1 s0 s1 s2 s3 i n) (< i n))
      (R1 s0 (+ s1 2) s2 s3 (+ i 1) n))))

;; progress
;; R1(s0, s1, s2, s3, i, n) /\ i >= n => R2(s0, s1, s2, s3, 0, n)
(assert (forall ((s0 Int) (s1 Int) (s2 Int) (s3 Int) (i Int) (n Int))
  (=> (and (R1 s0 s1 s2 s3 i n) (>= i n))
      (R2 s0 s1 s2 s3 0 n))))

;; loop invariant
;; R2(s0, s1, s2 + 1, s3 + 2, i + 1, n) /\ i < n => R2(s0, s1, s2, s3, i, n)
(assert (forall ((s0 Int) (s1 Int) (s2 Int) (s3 Int) (i Int) (n Int))
  (=> (and (R2 s0 s1 s2 s3 i n) (< i n))
      (R2 s0 s1 (+ s2 1) (+ s3 2) (+ i 1) n))))

;; simultaneous summary R
(assert (forall ((s0_0 Int) (s1_0 Int) (s2_0 Int) (s3_0 Int) (i_0 Int)
                 (s0_1 Int) (s1_1 Int) (s2_1 Int) (s3_1 Int) (i_1 Int)
                 (s0_2 Int) (s1_2 Int) (s2_2 Int) (s3_2 Int) (i_2 Int)
                 (n Int))
  (=> (and
        (R0 s0_0 s1_0 s2_0 s3_0 0 n)
        (R1 s0_1 s1_1 s2_1 s3_1 0 n)
        (R2 s0_2 s1_2 s2_2 s3_2 0 n))
    (R s0_0 s1_0 s2_0 s3_0 0
       s0_1 s1_1 s2_1 s3_1 0
       s0_2 s1_2 s2_2 s3_2 0 n))))

;; the simultaneous summary supports the individual summaries
(assert (forall ((s0_0 Int) (s1_0 Int) (s2_0 Int) (s3_0 Int) (i_0 Int)
                 (s0_1 Int) (s1_1 Int) (s2_1 Int) (s3_1 Int) (i_1 Int)
                 (s0_2 Int) (s1_2 Int) (s2_2 Int) (s3_2 Int) (i_2 Int)
                 (n Int))
  (=>
    (R s0_0 s1_0 s2_0 s3_0 i_0
       s0_1 s1_1 s2_1 s3_1 i_1
       s0_2 s1_2 s2_2 s3_2 i_2 n)
    (R0 s0_0 s1_0 s2_0 s3_0 i_0 n))))

(assert (forall ((s0_0 Int) (s1_0 Int) (s2_0 Int) (s3_0 Int) (i_0 Int)
                 (s0_1 Int) (s1_1 Int) (s2_1 Int) (s3_1 Int) (i_1 Int)
                 (s0_2 Int) (s1_2 Int) (s2_2 Int) (s3_2 Int) (i_2 Int)
                 (n Int))
  (=>
    (R s0_0 s1_0 s2_0 s3_0 i_0
       s0_1 s1_1 s2_1 s3_1 i_1
       s0_2 s1_2 s2_2 s3_2 i_2 n)
    (R1 s0_1 s1_1 s2_1 s3_1 i_1 n))))

(assert (forall ((s0_0 Int) (s1_0 Int) (s2_0 Int) (s3_0 Int) (i_0 Int)
                 (s0_1 Int) (s1_1 Int) (s2_1 Int) (s3_1 Int) (i_1 Int)
                 (s0_2 Int) (s1_2 Int) (s2_2 Int) (s3_2 Int) (i_2 Int)
                 (n Int))
  (=>
    (R s0_0 s1_0 s2_0 s3_0 i_0
       s0_1 s1_1 s2_1 s3_1 i_1
       s0_2 s1_2 s2_2 s3_2 i_2 n)
    (R2 s0_2 s1_2 s2_2 s3_2 i_2 n))))

;; loop invariant
;; R( s0_0 + 1, s1_0, s2_0, s3_0, i_0 + 1, n_0
;;  , s0_1, s1_1 + 2, s2_1, s3_1, i_1 + 1, n_1
;;  , s0_2, s1_2, s2_2 + 1, s3_2 + 2, i_2 + 1, n_2
;;  ) /\ i_0 < n_0 /\ i_1 < n_1 /\ i_2 < n_2
;;  => R( s0_0, s1_0, s2_0, s3_0, i_0, n_0
;;      , s0_1, s1_1, s2_1, s3_1, i_1, n_1
;;      , s0_2, s1_2, s2_2, s3_2, i_2, n_2
;;      )
(assert (forall ((s0_0 Int) (s1_0 Int) (s2_0 Int) (s3_0 Int) (i_0 Int)
                 (s0_1 Int) (s1_1 Int) (s2_1 Int) (s3_1 Int) (i_1 Int)
                 (s0_2 Int) (s1_2 Int) (s2_2 Int) (s3_2 Int) (i_2 Int)
                 (n Int))
  (=> (and
      (R s0_0 s1_0 s2_0 s3_0 i_0
         s0_1 s1_1 s2_1 s3_1 i_1
         s0_2 s1_2 s2_2 s3_2 i_2 n)
      (< i_0 n)
      (< i_1 n)
      (< i_2 n))
    (R (+ s0_0 1) s1_0 s2_0 s3_0 (+ i_0 1)
       s0_1 (+ s1_1 2) s2_1 s3_1 (+ i_1 1)
       s0_2 s1_2 (+ s2_2 1) (+ s3_2 2) (+ i_2 1) n))))

;; query
;; R( s0_0, s1_0, s2_0, s3_0, i_0, n_0
;;  , s0_1, s1_1, s2_1, s3_1, i_1, n_1
;;  , s0_2, s1_2, s2_2, s3_2, i_2, n_2
;;  ) /\ i_0 >= n_0 /\ i_1 >= n_1 /\ i_2 /\ n_2
;;  => s0_2 = s2_2 /\ s1_2 = s3_2
(assert (forall ((s0_0 Int) (s1_0 Int) (s2_0 Int) (s3_0 Int) (i_0 Int)
                 (s0_1 Int) (s1_1 Int) (s2_1 Int) (s3_1 Int) (i_1 Int)
                 (s0_2 Int) (s1_2 Int) (s2_2 Int) (s3_2 Int) (i_2 Int)
                 (n Int))
  (=> (and
    (R s0_0 s1_0 s2_0 s3_0 i_0
       s0_1 s1_1 s2_1 s3_1 i_1
       s0_2 s1_2 s2_2 s3_2 i_2 n)
      (>= i_0 n)
      (>= i_1 n)
      (>= i_2 n))
    (and (= s0_2 s2_2) (= s1_2 s3_2)))))


;; A valid and sufficient model for R:
;; R( s0_0, s1_0, s2_0, s3_0, i_0
;;  , s0_1, s1_1, s2_1, s3_1, i_1
;;  , s0_2, s1_2, s2_2, s3_2, i_2
;;  , n
;;  ) := i_0 = i_1
;;    /\ i_0 = i_2
;;    /\ s0_0 = s2_2
;;    /\ s1_1 = s3_2
;;    /\ (i_0 >= n => s0_0 = s0_2)
;;    /\ (i_1 >= n => s1_1 = s1_2)

(check-sat)
(get-model)
