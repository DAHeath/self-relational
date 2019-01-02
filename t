(set-logic HORN)
(set-option :fixedpoint.engine "duality")


(assert (forall ((V0 Int) (x_0 Int))
   (=> (and (= V0 0) (= x_0 0) (< x_0 0)) false)))

(assert (forall ((V1 Int) (x_0 Int))
   (=> (and (not (= V1 0)) (= x_0 1) (< x_0 0)) false)))


(check-sat)
(get-model)

