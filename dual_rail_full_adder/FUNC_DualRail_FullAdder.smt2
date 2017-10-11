(set-logic QF_BV)

; Inputs
(declare-fun X   () (_ BitVec 2))
(declare-fun Y   () (_ BitVec 2))
(declare-fun Cin () (_ BitVec 2))

; Outputs
(declare-fun S     () (_ BitVec 2))
(declare-fun Cout  () (_ BitVec 2))

; The result of Cout1 S1
(declare-fun RegS  () (_ BitVec 2))

; The result of Cout0 S0
(declare-fun nRegS () (_ BitVec 2))

(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 0 0) a)
)

(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 1 1) a)
)

(define-fun Th23 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1))) (_ BitVec 1)
    (ite
        (=
            (_ bv1 1)
            (bvand
                (bvnot a)
                (bvnot b)
                (bvnot c)))
        (_ bv0 1)
        (ite
            (=
                (_ bv1 1)
                (bvor
                    (bvand a b)
                    (bvand b c)
                    (bvand a c)))
            (_ bv1 1)
            (_ bv0 1)))
)

(define-fun Th35w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1))) (_ BitVec 1)
    (ite
        (=
            (_ bv1 1)
            (bvand
                (bvnot a)
                (bvnot b)
                (bvnot c)
                (bvnot d)))
        (_ bv0 1)
        (ite
            (=
                (_ bv1 1)
                (bvor
                    (bvand a b)
                    (bvand a c)
                    (bvand a d)
                    (bvand b c d)))
            (_ bv1 1)
            (_ bv0 1)))
)

(assert
    (not
        (let
            (
                (Cout1 (Th23 (rail1 X) (rail1 Y) (rail1 Cin)))
                (Cout0 (Th23 (rail0 X) (rail0 Y) (rail0 Cin)))
                (S1 (Th35w2 (Th23 (rail0 X) (rail0 Y) (rail0 Cin)) (rail1 X) (rail1 Y) (rail1 Cin)))
                (S0 (Th35w2 (Th23 (rail1 X) (rail1 Y) (rail1 Cin)) (rail0 X) (rail0 Y) (rail0 Cin))))
            (=>
                (and
                    (= (concat S1 S0) S)
                    (= (concat Cout1 Cout0) Cout)
                    (= (concat Cout1 S1) RegS)
                    (= (concat Cout0 S0) nRegS)
                    (not (= (_ bv3 2) X))
                    (not (= (_ bv3 2) Y))
                    (not (= (_ bv3 2) Cin))
                    (not (= (_ bv0 2) X))
                    (not (= (_ bv0 2) Y))
                    (not (= (_ bv0 2) Cin)))
                (and
                    (= (concat Cout1 S1) (bvadd (concat (_ bv0 1) (rail1 X)) (concat (_ bv0 1) (rail1 Y)) (concat (_ bv0 1) (rail1 Cin))))
                    (not (= S1 S0))
                    (not (= Cout1 Cout0))))))
)

(check-sat)
(get-model)

(assert
    (not
        (let
            (
                (Cout1 (Th23 (rail1 X) (rail1 Y) (rail1 Cin)))
                (Cout0 (Th23 (rail0 X) (rail0 Y) (rail0 Cin)))
                (S1 (Th35w2 (Th23 (rail0 X) (rail0 Y) (rail0 Cin)) (rail1 X) (rail1 Y) (rail1 Cin)))
                (S0 (Th35w2 (Th23 (rail1 X) (rail1 Y) (rail1 Cin)) (rail0 X) (rail0 Y) (rail0 Cin))))
            (=>
                (and
                    (= (concat S1 S0) S)
                    (= (concat Cout1 Cout0) Cout)
                    (= (concat Cout1 S1) RegS)
                    (= (concat Cout0 S0) nRegS)
                    (= (_ bv0 2) X)
                    (= (_ bv0 2) Y)
                    (= (_ bv0 2) Cin))
                (and
                    (= (_ bv0 2) S)
                    (= (_ bv0 2) Cout)))))
)

(check-sat)
(get-model)
