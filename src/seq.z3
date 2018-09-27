;; Consider the following solution to this triple, assuming the simplier
;; partition rule:
;;
;; {x = 0} x := x+1 ; x := x+1 {x = 2}
;; CONSEQUENCE
;; {x + 2 = 2} x := x+1 ; x := x+1 {x = 2}
;;   BURDEN: x = 0 => x + 2 = 2
;;           trivial
;; PARTITION (using separate names, but this is not necessary)
;; {x + 2 = 2 | y + 1 = 2} x := x+1 * y := y+1 {x + 1 = 2 | y = 2}
;; SPLIT
;; {x + 2 = 2} x := x+1 {x + 1 = 2}
;; {y + 1 = 2} y := y+1 {y = 2}
;;   BURDEN: x + 2 = 2 /\ y + 1 = 2 => x + 2 = 2
;;           x + 2 = 2 /\ y + 1 = 2 => y + 1 = 2
;;           x + 1 = 2 /\ y = 2 => x + 1 = 2 /\ y = 2
;;           trivial
;; {x + 2 = 2} x := x+1 {x + 1 = 2}
;; ASSIGN
;; {y + 1 = 2} y := y+1 {y = 2}
;; ASSIGN

;; The proof system as is would also require the following proof due to the partition:
;; {x + 2 = 2} x := x + 1 {x + 1 = 2}
;; ASSIGN

;; Let's repeat the proof, but say we don't know the intermediate propositions:
;;
;; {x = 0} x := x+1 ; x := x+1 {x = 2}
;; CONSEQUENCE
;; {R0(x)} x := x+1 ; x := x+1 {R1(x)}
;;   BURDEN: x = 0 => R0(x)
;;           R1(x) => x = 2
;; PARTITION (when converting to CHC a naming scheme is necessary)
;; {R0(x) | R2(y)} x := x+1 * y := y + 1 {R2(x) | R1(y)}
;; CONSEQUENCE (for good measure)
;; {R3(x, y)} x := x+1 * y := y + 1 {R4(x, y)}
;;   BURDEN: R0(x) /\ R2(y) => R3(x, y)
;;           R4(x, y) => R2(x)
;;           R4(x, y) => R1(y)
;; SPLIT
;; {R5(x+1)} x := x + 1 {R5(x)}
;; {R6(y+1)} y := y + 1 {R6(y)}
;;   BURDEN: R3(x, y) => R5(x+1)
;;           R3(x, y) => R6(y+1)
;;           R5(x) /\ R6(y) => R4(x, y)
;; {R5(x+1)} x := x + 1 {R5(x)}
;; ASSIGN
;; {R6(y+1)} y := y + 1 {R6(y)}
;; ASSIGN

;; Accounting for the additional proof term adds this:
;; {R0(x)} x := x+1 {R2(x)}
;; CONSEQUENCE
;; {R2(x+1)} x := x+1 {R2(x)}
;;   BURDEN: R0(x) => R2(x+1)

(set-logic HORN)

(declare-fun R0 (Int) Bool)
(declare-fun R1 (Int) Bool)
(declare-fun R2 (Int) Bool)
(declare-fun R3 (Int Int) Bool)
(declare-fun R4 (Int Int) Bool)
(declare-fun R5 (Int) Bool)
(declare-fun R6 (Int) Bool)

;; x = 0 => R0(x)
(assert (forall ((x Int)) (=> (= x 0) (R0 x))))

;; R1(x) => x = 2
(assert (forall ((x Int)) (=> (R1 x) (= x 2))))

;; R0(x) /\ R2(y) => R3(x, y)
(assert (forall ((x Int) (y Int))
  (=> (and (R0 x) (R2 y)) (R3 x y))))

;; R4(x, y) => R2(x)
(assert (forall ((x Int) (y Int))
  (=> (R4 x y) (R2 x))))

;; R4(x, y) => R1(y)
(assert (forall ((x Int) (y Int))
  (=> (R4 x y) (R1 y))))

;; R3(x, y) => R5(x+1)
(assert (forall ((x Int) (y Int))
  (=> (R3 x y) (R5 (+ x 1)))))

;; R3(x, y) => R6(y+1)
(assert (forall ((x Int) (y Int))
  (=> (R3 x y) (R6 (+ y 1)))))

;; R5(x) /\ R6(y) => R4(x, y)
(assert (forall ((x Int) (y Int))
  (=> (and (R5 x) (R6 y)) (R4 x y))))

;; R0(x) => R2(x+1)
RUNNING THE SYSTEM WITHOUT THIS ASSERTION GIVES AN INVALID ANSWER
; (assert (forall ((x Int))
;   (=> (R0 x) (R2 (+ x 1)))))

(check-sat)
(get-model)
