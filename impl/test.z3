(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R (Int) Bool)

(assert (R 1))
(assert
  (forall ((x Int))
    (=>
      (and
        (R x)
        (not (= x 1)))
      false)))

(check-sat)
(get-model)
