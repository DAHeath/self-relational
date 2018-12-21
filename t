(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int) Bool)

(assert (forall ((n_0 Int))
   (R0 0 0 n_0)))

(assert (forall ((a_0 Int) (b_0 Int) (n_0 Int))
   (=> (and (< b_0 n_0) (R0 a_0 b_0 n_0)) (R0 (+ a_0 (+ b_0 1)) (+ b_0 1) n_0))))

(assert (forall ((a_0 Int) (b_0 Int) (n_0 Int))
   (=> (and (and (< a_0 n_0) (>= b_0 n_0)) (R0 a_0 b_0 n_0)) false)))


(check-sat)
(get-model)

