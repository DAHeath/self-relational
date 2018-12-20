(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int) Bool)
(declare-fun R1 (Int) Bool)
(declare-fun R2 (Int) Bool)

(assert (=> true (R2 0)))

(assert (forall ((x_0 Int))
   (=> (R2 x_0) (R1 (+ x_0 1)))))

(assert (forall ((x_0 Int))
   (=> (R1 x_0) (R0 (+ x_0 1)))))

(assert (forall ((x_0 Int))
   (=> (and (R0 x_0) (not (= x_0 2))) false)))


(check-sat)
(get-model)

