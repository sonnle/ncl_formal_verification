; Formal verification proof of input completeness of NCL 2-bit Full Adder
(set-logic QF_BV)

; Inputs
(declare-fun X     () (_ BitVec 2))
(declare-fun Y     () (_ BitVec 2))
(declare-fun Cin   () (_ BitVec 2))

(declare-fun X_d     () (_ BitVec 2))
(declare-fun Y_d     () (_ BitVec 2))
(declare-fun Cin_d   () (_ BitVec 2))

; Extract rail0 of a dual rail signal
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 0 0) a)
)

; Extract rail1 of a dual rail signal
(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 1 1) a)
)

; Determine if the dual rail signal is null (0x00)
(define-fun nullp ((a (_ BitVec 2))) (Bool)
    (and
        (= (_ bv0 1) (rail0 a))
        (= (_ bv0 1) (rail1 a)))
)

(define-fun datap ((a (_ BitVec 2))) (Bool)
    (or
        (= (_ bv1 2) a)
        (= (_ bv2 2) a)
    )
)

; Determine if the dual rail signal is valid (not 0x11)
(define-fun legalp ((a (_ BitVec 2))) (Bool)
    (not
        (and
            (= (_ bv1 1) (rail0 a))
            (= (_ bv1 1) (rail1 a))))
)

(define-fun Th23 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
            g_l))
)

(define-fun Th34w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
            g_l))
)

(declare-fun Gc_0 () (_ BitVec 1))

(assert
    (not
        (let
            (
                (Gd_0 (Th23 (rail0 Cin) (rail0 X) (rail0 Y) Gc_0))
                (Gd_1 (Th23 (rail1 Cin) (rail1 X) (rail1 Y) Gc_0))
            )
        (let
            (
                (Gd_2 (Th34w2 Gd_1 (rail0 Cin) (rail0 X) (rail0 Y) Gc_0))
                (Gd_3 (Th34w2 Gd_0 (rail1 Cin) (rail1 X) (rail1 Y) Gc_0))
            )
        (let
            (
                (Gn_0 (Th23 (rail0 Cin_d) (rail0 X_d) (rail0 Y_d) Gd_0))
                (Gn_1 (Th23 (rail1 Cin_d) (rail1 X_d) (rail1 Y_d) Gd_1))
            )
        (let
            (
                (Gn_2 (Th34w2 Gn_1 (rail0 Cin_d) (rail0 X_d) (rail0 Y_d) Gd_2))
                (Gn_3 (Th34w2 Gn_0 (rail1 Cin_d) (rail1 X_d) (rail1 Y_d) Gd_3))
            )
        (let
            (
                (Cout (concat Gn_1 Gn_0))
                (S    (concat Gn_3 Gn_2))
            )
        (=>
            (and
                (datap X)
                (datap Y)
                (datap Cin)
                (not (= (_ bv3 2) X_d))
                (not (= (_ bv3 2) Y_d))
                (not (= (_ bv3 2) Cin_d))
                (= (_ bv0 1) Gc_0)
                (or
                    (or
                        (nullp X_d)
                        (= X X_d)
                    )
                    (or
                        (nullp Y_d)
                        (= Y Y_d)
                    )
                    (or
                        (nullp Cin_d)
                        (= Cin Cin_d)
                    )
                )
                (or
                    (datap X_d)
                    (datap Y_d)
                    (datap Cin_d)))
            (or (datap S)
                (datap Cout)))))))))
)
(check-sat)
(get-model)
