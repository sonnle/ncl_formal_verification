; Formal verification proof of input completeness of NCL circuit
(set-logic QF_BV)

; Inputs
(declare-fun A () (_ BitVec 2))
(declare-fun B () (_ BitVec 2))
(declare-fun C () (_ BitVec 2))

; Outputs
(declare-fun X_t () (_ BitVec 2))
(declare-fun Y_t () (_ BitVec 2))

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
        (= (_ bv0 1) (rail1 a))
    )
)

; determine if the dual rail signal is valid (not 0x11)
(define-fun legalp ((a (_ BitVec 2))) (Bool)
    (not
        (and
            (= (_ bv1 1) (rail0 a))
            (= (_ bv1 1) (rail1 a))
        )
    )
)

(define-fun Th22 ((a (_ BitVec 1)) (b (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
    (ite
        (=
            (_ bv1 1)
            (bvand
                (bvnot a)
                (bvnot b)))
        (_ bv0 1)
        (ite
            (=
                (_ bv1 1)
                (bvand a b))
            (_ bv1 1)
            g_l))
)

(define-fun Th33 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
                (bvand a b c))
            (_ bv1 1)
            g_l))
)

(define-fun Th23w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
                (bvor a
                    (bvand b c)))
            (_ bv1 1)
            g_l))
)

(define-fun Th24comp ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
                    (bvand a c)
                    (bvand b c)
                    (bvand a d)
                    (bvand b d)))
            (_ bv1 1)
            g_l))
)

(define-fun Thxor0 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
                    (bvand c d)))
            (_ bv1 1)
            g_l))
)

(define-fun Thand0 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
                    (bvand b c)
                    (bvand a d)))
            (_ bv1 1)
            g_l))
)

(declare-fun Gc_0 () (_ BitVec 1))
(declare-fun Gc_1 () (_ BitVec 1))
(declare-fun Gc_2 () (_ BitVec 1))
(declare-fun Gc_3 () (_ BitVec 1))
(declare-fun Gc_4 () (_ BitVec 1))
(declare-fun Gc_5 () (_ BitVec 1))

(assert
    (not
        (let
            (
                (Gn_0 (Th24comp (rail0 B) (rail0 C) (rail1 C) (rail1 B) Gc_0))
                (Gn_1 (Th22 (rail1 A) (rail1 B) Gc_1))
                (Gn_2 (Thxor0 (rail0 A) (rail0 C) (rail1 A) (rail1 C) Gc_2))
                (Gn_3 (Th33 (rail1 C) (rail0 A) (rail0 B) Gc_3))
            )
        (let
            (
                (X (concat (Thand0 Gn_1 (rail0 A) (rail0 B) (rail1 C) Gc_4) Gn_0))
                (Y (concat (Th23w2 Gn_3 Gn_1 (rail0 C) Gc_5) Gn_2))
            )
        (=>
            (and
                (= X X_t)
                (= Y Y_t)
                (not (= (_ bv3 2) A))
                (not (= (_ bv3 2) B))
                (not (= (_ bv3 2) C))
                (= (_ bv0 1) Gc_0)
                (= (_ bv0 1) Gc_1)
                (= (_ bv0 1) Gc_2)
                (= (_ bv0 1) Gc_3)
                (= (_ bv0 1) Gc_4)
                (= (_ bv0 1) Gc_5)
                (or
                    (nullp A)
                    (nullp B)
                    (nullp C)))
            (or
                (nullp X)
                (nullp Y))))))
)

(check-sat)
(get-model)
