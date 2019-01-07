(set-logic HORN)
(set-option :fixedpoint.engine "duality")

(declare-fun R0 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R1 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R2 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R3 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R4 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R5 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(declare-fun R6 (Int Int Int Int Int Int Int Int Int Int Int Int) Bool)

(assert (forall ((a_0 Int) (a_1 Int) (a_2 Int) (b_0 Int) (b_1 Int) (b_2 Int) (c_0 Int) (c_1 Int) (c_2 Int) (d_0 Int) (d_1 Int) (d_2 Int) (i_0 Int) (i_1 Int) (i_2 Int) (n_0 Int) (n_1 Int) (n_2 Int))
   (=> (and (= a_0 0) (= b_0 0) (= i_0 0) (= a_0 a_1) (= b_0 b_1) (= c_0 c_1) (= d_0 d_1) (= i_0 i_1) (= n_0 n_1) (= a_1 a_2) (= b_1 b_2) (= c_1 c_2) (= d_1 d_2) (= i_1 i_2) (= n_1 n_2)) (R0 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_2 b_2 c_2 d_2 i_2 n_2))))

(assert (forall ((V3 Int) (V4 Int) (a_0 Int) (a_1 Int) (a_2 Int) (b_0 Int) (b_1 Int) (b_2 Int) (c_0 Int) (c_1 Int) (c_2 Int) (d_0 Int) (d_1 Int) (d_2 Int) (i_0 Int) (i_1 Int) (i_2 Int) (n_0 Int) (n_1 Int) (n_2 Int))
   (=> (and (R0 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 V3 b_2 c_2 d_2 V4 n_2) (< V4 n_2) (= a_2 (+ V3 V4)) (= i_2 (+ V4 1))) (R0 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_2 b_2 c_2 d_2 i_2 n_2))))

(assert (forall ((V5 Int) (a_0 Int) (a_1 Int) (a_2 Int) (b_0 Int) (b_1 Int) (b_2 Int) (c_0 Int) (c_1 Int) (c_2 Int) (d_0 Int) (d_1 Int) (d_2 Int) (i_0 Int) (i_1 Int) (i_2 Int) (n_0 Int) (n_1 Int) (n_2 Int))
   (=> (and (R0 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_2 b_2 c_2 d_2 V5 n_2) (not (< V5 n_2)) (= i_2 0)) (R1 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_2 b_2 c_2 d_2 i_2 n_2))))

(assert (forall ((V10 Int) (V11 Int) (V12 Int) (V13 Int) (V6 Int) (V7 Int) (V8 Int) (V9 Int) (a_0 Int) (a_1 Int) (a_2 Int) (b_0 Int) (b_1 Int) (b_2 Int) (c_0 Int) (c_1 Int) (c_2 Int) (d_0 Int) (d_1 Int) (d_2 Int) (i_0 Int) (i_1 Int) (i_2 Int) (n_0 Int) (n_1 Int) (n_2 Int))
   (=> (or 
(and (R1 a_0 b_0 c_0 d_0 i_0 n_0 V6 b_1 c_1 d_1 V7 n_1 a_2 b_2 c_2 d_2 i_2 n_2) (not (< i_2 n_2)) (< V7 n_1) (= a_1 (+ V6 V7)) (= i_1 (+ V7 1))) 
(and (R1 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_2 V8 c_2 d_2 V9 n_2) (< V9 n_2) (= b_2 (+ V8 V9)) (= i_2 (+ V9 1)) (not (< i_1 n_1))) 
(and (R1 a_0 b_0 c_0 d_0 i_0 n_0 V12 b_1 c_1 d_1 V13 n_1 a_2 V10 c_2 d_2 V11 n_2) (< V11 n_2) (= b_2 (+ V10 V11)) (= i_2 (+ V11 1)) (< V13 n_1) (= a_1 (+ V12 V13)) (= i_1 (+ V13 1)))) (R1 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_2 b_2 c_2 d_2 i_2 n_2))))

(assert (forall ((V14 Int) (a_0 Int) (a_1 Int) (a_2 Int) (b_0 Int) (b_1 Int) (b_2 Int) (c_0 Int) (c_1 Int) (c_2 Int) (d_0 Int) (d_1 Int) (d_2 Int) (i_0 Int) (i_1 Int) (i_2 Int) (n_0 Int) (n_1 Int) (n_2 Int))
   (=> (and (R1 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 V14 n_1 a_2 b_2 c_2 d_2 i_2 n_2) (not (< i_2 n_2)) (not (< V14 n_1)) (= i_1 0)) (R2 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_2 b_2 c_2 d_2 i_2 n_2))))

(assert (forall ((V15 Int) (V16 Int) (a_0 Int) (a_1 Int) (a_2 Int) (b_0 Int) (b_1 Int) (b_2 Int) (c_0 Int) (c_1 Int) (c_2 Int) (d_0 Int) (d_1 Int) (d_2 Int) (i_0 Int) (i_1 Int) (i_2 Int) (n_0 Int) (n_1 Int) (n_2 Int))
   (=> (and (R2 a_0 b_0 c_0 d_0 i_0 n_0 a_1 V15 c_1 d_1 V16 n_1 a_2 b_2 c_2 d_2 i_2 n_2) (< V16 n_1) (= b_1 (+ V15 V16)) (= i_1 (+ V16 1))) (R2 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_2 b_2 c_2 d_2 i_2 n_2))))

(assert (forall ((V17 Int) (V18 Int) (V19 Int) (a_0 Int) (a_1 Int) (a_2 Int) (a_3 Int) (a_4 Int) (b_0 Int) (b_1 Int) (b_2 Int) (b_3 Int) (b_4 Int) (c_0 Int) (c_1 Int) (c_2 Int) (c_3 Int) (c_4 Int) (d_0 Int) (d_1 Int) (d_2 Int) (d_3 Int) (d_4 Int) (i_0 Int) (i_1 Int) (i_2 Int) (i_3 Int) (i_4 Int) (n_0 Int) (n_1 Int) (n_2 Int) (n_3 Int) (n_4 Int))
   (=> (and (R2 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 V17 V18 V19 n_1 a_2 b_2 c_2 d_2 i_2 n_2) (not (< V19 n_1)) (= a_1 a_2) (= b_1 b_2) (= V17 c_2) (= V18 d_2) (= V19 i_2) (= n_1 n_2) (= c_1 0) (= d_1 0) (= i_1 0) (= a_1 a_3) (= b_1 b_3) (= c_1 c_3) (= d_1 d_3) (= i_1 i_3) (= n_1 n_3) (= a_0 a_4) (= b_0 b_4) (= c_0 c_4) (= d_0 d_4) (= i_0 i_4) (= n_0 n_4)) (R3 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4))))

(assert (forall ((V20 Int) (V21 Int) (V22 Int) (V23 Int) (V24 Int) (V25 Int) (V26 Int) (V27 Int) (V28 Int) (V29 Int) (a_0 Int) (a_1 Int) (a_3 Int) (a_4 Int) (b_0 Int) (b_1 Int) (b_3 Int) (b_4 Int) (c_0 Int) (c_1 Int) (c_3 Int) (c_4 Int) (d_0 Int) (d_1 Int) (d_3 Int) (d_4 Int) (i_0 Int) (i_1 Int) (i_3 Int) (i_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int))
   (=> (or 
(and (R3 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 V20 b_4 c_4 d_4 V21 n_4) (not (< i_3 n_3)) (< V21 n_4) (= a_4 (+ V20 V21)) (= i_4 (+ V21 1))) 
(and (R3 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 V22 V23 V24 n_3 a_4 b_4 c_4 d_4 i_4 n_4) (< V24 n_3) (= c_3 (+ V22 V24)) (= d_3 (+ V23 V24)) (= i_3 (+ V24 1)) (not (< i_4 n_4))) 
(and (R3 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 V25 V26 V27 n_3 V28 b_4 c_4 d_4 V29 n_4) (< V27 n_3) (= c_3 (+ V25 V27)) (= d_3 (+ V26 V27)) (= i_3 (+ V27 1)) (< V29 n_4) (= a_4 (+ V28 V29)) (= i_4 (+ V29 1)))) (R3 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4))))

(assert (forall ((V30 Int) (a_0 Int) (a_1 Int) (a_3 Int) (a_4 Int) (b_0 Int) (b_1 Int) (b_3 Int) (b_4 Int) (c_0 Int) (c_1 Int) (c_3 Int) (c_4 Int) (d_0 Int) (d_1 Int) (d_3 Int) (d_4 Int) (i_0 Int) (i_1 Int) (i_3 Int) (i_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int))
   (=> (and (R3 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 V30 n_4) (not (< i_3 n_3)) (not (< V30 n_4)) (= i_4 0)) (R4 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4))))

(assert (forall ((V31 Int) (V32 Int) (V33 Int) (V34 Int) (V35 Int) (V36 Int) (V37 Int) (V38 Int) (V39 Int) (V40 Int) (V41 Int) (V42 Int) (V43 Int) (V44 Int) (V45 Int) (V46 Int) (V47 Int) (V48 Int) (V49 Int) (V50 Int) (V51 Int) (V52 Int) (V53 Int) (V54 Int) (V55 Int) (V56 Int) (V57 Int) (V58 Int) (a_0 Int) (a_1 Int) (a_3 Int) (a_4 Int) (b_0 Int) (b_1 Int) (b_3 Int) (b_4 Int) (c_0 Int) (c_1 Int) (c_3 Int) (c_4 Int) (d_0 Int) (d_1 Int) (d_3 Int) (d_4 Int) (i_0 Int) (i_1 Int) (i_3 Int) (i_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int))
   (=> (or 
(and (R4 V31 b_0 c_0 d_0 V32 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4) (not (< i_4 n_4)) (not (< i_1 n_1)) (< V32 n_0) (= a_0 (+ V31 V32)) (= i_0 (+ V32 1))) 
(and (R4 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 V33 V34 V35 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4) (not (< i_4 n_4)) (< V35 n_1) (= c_1 (+ V33 V35)) (= d_1 (+ V34 V35)) (= i_1 (+ V35 1)) (not (< i_0 n_0))) 
(and (R4 V39 b_0 c_0 d_0 V40 n_0 a_1 b_1 V36 V37 V38 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4) (not (< i_4 n_4)) (< V38 n_1) (= c_1 (+ V36 V38)) (= d_1 (+ V37 V38)) (= i_1 (+ V38 1)) (< V40 n_0) (= a_0 (+ V39 V40)) (= i_0 (+ V40 1))) 
(and (R4 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 V41 c_4 d_4 V42 n_4) (< V42 n_4) (= b_4 (+ V41 V42)) (= i_4 (+ V42 1)) (not (< i_1 n_1)) (not (< i_0 n_0))) 
(and (R4 V45 b_0 c_0 d_0 V46 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 V43 c_4 d_4 V44 n_4) (< V44 n_4) (= b_4 (+ V43 V44)) (= i_4 (+ V44 1)) (not (< i_1 n_1)) (< V46 n_0) (= a_0 (+ V45 V46)) (= i_0 (+ V46 1))) 
(and (R4 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 V49 V50 V51 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 V47 c_4 d_4 V48 n_4) (< V48 n_4) (= b_4 (+ V47 V48)) (= i_4 (+ V48 1)) (< V51 n_1) (= c_1 (+ V49 V51)) (= d_1 (+ V50 V51)) (= i_1 (+ V51 1)) (not (< i_0 n_0))) 
(and (R4 V57 b_0 c_0 d_0 V58 n_0 a_1 b_1 V54 V55 V56 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 V52 c_4 d_4 V53 n_4) (< V53 n_4) (= b_4 (+ V52 V53)) (= i_4 (+ V53 1)) (< V56 n_1) (= c_1 (+ V54 V56)) (= d_1 (+ V55 V56)) (= i_1 (+ V56 1)) (< V58 n_0) (= a_0 (+ V57 V58)) (= i_0 (+ V58 1)))) (R4 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4))))

(assert (forall ((V59 Int) (a_0 Int) (a_1 Int) (a_3 Int) (a_4 Int) (b_0 Int) (b_1 Int) (b_3 Int) (b_4 Int) (c_0 Int) (c_1 Int) (c_3 Int) (c_4 Int) (d_0 Int) (d_1 Int) (d_3 Int) (d_4 Int) (i_0 Int) (i_1 Int) (i_3 Int) (i_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int))
   (=> (and (R4 a_0 b_0 c_0 d_0 V59 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4) (not (< i_4 n_4)) (not (< i_1 n_1)) (not (< V59 n_0)) (= i_0 0)) (R5 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4))))

(assert (forall ((V60 Int) (V61 Int) (a_0 Int) (a_1 Int) (a_3 Int) (a_4 Int) (b_0 Int) (b_1 Int) (b_3 Int) (b_4 Int) (c_0 Int) (c_1 Int) (c_3 Int) (c_4 Int) (d_0 Int) (d_1 Int) (d_3 Int) (d_4 Int) (i_0 Int) (i_1 Int) (i_3 Int) (i_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int))
   (=> (and (R5 a_0 V60 c_0 d_0 V61 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4) (< V61 n_0) (= b_0 (+ V60 V61)) (= i_0 (+ V61 1))) (R5 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4))))

(assert (forall ((V62 Int) (V63 Int) (V64 Int) (a_0 Int) (a_1 Int) (a_3 Int) (a_4 Int) (b_0 Int) (b_1 Int) (b_3 Int) (b_4 Int) (c_0 Int) (c_1 Int) (c_3 Int) (c_4 Int) (d_0 Int) (d_1 Int) (d_3 Int) (d_4 Int) (i_0 Int) (i_1 Int) (i_3 Int) (i_4 Int) (n_0 Int) (n_1 Int) (n_3 Int) (n_4 Int))
   (=> (and (R5 a_0 b_0 V62 V63 V64 n_0 a_1 b_1 c_1 d_1 i_1 n_1 a_3 b_3 c_3 d_3 i_3 n_3 a_4 b_4 c_4 d_4 i_4 n_4) (not (< V64 n_0)) (= a_1 a_3) (= b_1 b_3) (= c_1 c_3) (= d_1 d_3) (= i_1 i_3) (= n_1 n_3) (= a_0 a_4) (= b_0 b_4) (= V62 c_4) (= V63 d_4) (= V64 i_4) (= n_0 n_4) (= c_0 0) (= d_0 0) (= i_0 0)) (R6 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1))))

(assert (forall ((V65 Int) (V66 Int) (V67 Int) (a_0 Int) (a_1 Int) (b_0 Int) (b_1 Int) (c_0 Int) (c_1 Int) (d_0 Int) (d_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int))
   (=> (and (R6 a_0 b_0 V65 V66 V67 n_0 a_1 b_1 c_1 d_1 i_1 n_1) (< V67 n_0) (= c_0 (+ V65 V67)) (= d_0 (+ V66 V67)) (= i_0 (+ V67 1))) (R6 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1))))

(assert (forall ((a_0 Int) (a_1 Int) (b_0 Int) (b_1 Int) (c_0 Int) (c_1 Int) (d_0 Int) (d_1 Int) (i_0 Int) (i_1 Int) (n_0 Int) (n_1 Int))
   (=> (and (R6 a_0 b_0 c_0 d_0 i_0 n_0 a_1 b_1 c_1 d_1 i_1 n_1) (not (< i_0 n_0)) (= a_0 a_1) (= b_0 b_1) (= c_0 c_1) (= d_0 d_1) (= i_0 i_1) (= n_0 n_1) (not (and (= a_0 c_0) (= b_0 d_0)))) false)))


(check-sat)
(get-model)

