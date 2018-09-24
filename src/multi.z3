(set-logic HORN)

(declare-fun R0 (Int) Bool)
(declare-fun R1 (Int) Bool)
(declare-fun R2 (Int) Bool)
(declare-fun R3 (Int) Bool)
(declare-fun R4 (Int) Bool)

(assert (R0 0))

(assert (forall ((x Int))
  (=> (R0 x) (R1 (+ x 1)))))

(assert (forall ((x Int) (x! Int))
  (=> (and (R0 x) (R1 x!)) (R3 (+ x 1)))))

(assert (forall ((x Int) (x! Int))
  (=> (and (R0 x) (R1 x!)) (R4 (+ x! 1)))))

(assert (forall ((x Int) (x! Int))
  (=> (and (R3 x) (R4 x!)) (R1 x))))

(assert (forall ((x Int) (x! Int))
  (=> (and (R3 x) (R4 x!)) (R2 x!))))

(assert (forall ((x Int))
  (=> (R2 x) (= x 2))))

(check-sat)
(get-model)
