(set-option :fixedpoint.engine duality)

(declare-rel R (Int Int))
(declare-rel q ())

(declare-var n Int)
(declare-var x Int)

(rule (R n 0))

(rule (=>
  (and
    (R n x)
    (< x n))
  (R n (+ 2 x))))

(rule (=>
  (not (=>
    (and
      (R n x)
      (>= x n))
    (not (= x 1))))
  q))

(query q :print-certificate true)
