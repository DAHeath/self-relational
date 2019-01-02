(set-logic HORN)
(set-option :fixedpoint.engine "duality")


(assert (forall ((POINT_0 Int) (V1 Int) (a_0 Int))
   (=> (and (= a_0 V1) (= POINT_0 (+ V1 1))) false)))


(check-sat)
(get-model)

