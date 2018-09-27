(set-logic HORN)
(set-option :fixedpoint.engine duality)

(declare-fun R (Int Int) Bool)

(assert
  (forall ((n Int))
    (R n 0)))

(assert
  (forall ((x Int) (n Int))
    (=>
      (and
        (R n x)
        (< x n))
      (R n (+ 2 x)))))

(assert
  (forall ((x Int) (n Int))
    (=>
      (and
        (R n x)
        (>= x n))
      (not (= x 41)))))

(check-sat)
(get-model)
