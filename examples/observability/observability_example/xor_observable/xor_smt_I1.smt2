; Formal verification proof - observability XOR
(set-logic QF_BV)

; Inputs: X, Y
(declare-fun X () (_ BitVec 2))
(declare-fun Y () (_ BitVec 2))

; Outputs: Z
(declare-fun Z () (_ BitVec 2))

; Extract rail0 of a dual rail signal
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 0 0) a)
)

; Extract rail1 of a dual rail signal
(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 1 1) a)
)

(define-fun datap ((a (_ BitVec 2))) (Bool)
    (or
        (= (_ bv1 2) a)
        (= (_ bv2 2) a)
    )
)

; Determine if the dual rail signal is null (0b00)
(define-fun nullp ((a (_ BitVec 2))) (Bool)
    (and
        (= (_ bv0 1) (rail0 a))
        (= (_ bv0 1) (rail1 a))
    )
)

; NCL Gate Boolean Function - TH22: (AB)
(define-fun th22 ((a (_ BitVec 1)) (b (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
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
            gl))
)

; NCL Gate Boolean Function - TH12: (A + B)
(define-fun th12 ((a (_ BitVec 1)) (b (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
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
                (bvor a b))
            (_ bv1 1)
            gl))
)

; NCL Gate Boolean Function - TH23w2: (A + BC)
(define-fun th23w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
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
            gl))
)


; Current values of threshold gates
(declare-fun Gc_0 () (_ BitVec 1))
(declare-fun Gc_1 () (_ BitVec 1))
(declare-fun Gc_2 () (_ BitVec 1))
(declare-fun Gc_3 () (_ BitVec 1))

(assert
    (not
        (let
            (
                (I0 (th22 (rail1 X) (rail1 Y) Gc_0))
                (I1 (th22 (rail1 X) (rail0 Y) Gc_1)))
        (let
            (
                (I2 (th23w2 I0 (rail0 X) (rail0 Y) Gc_2))
                (I3 (th23w2 (_ bv0 1) (rail0 X) (rail1 Y) Gc_3)))
        (let
            (
                (Z (concat I3 I2)))
        (=>
            (and
                (datap X)
                (datap Y)
                (= (bvand (rail1 X) (rail0 Y)) (_ bv1 1))
                (= (_ bv0 1) Gc_0)
                (= (_ bv0 1) Gc_1)
                (= (_ bv0 1) Gc_2)
                (= (_ bv0 1) Gc_3))
            (not
                (and
                    (datap Z)))))))
    )
)

(check-sat)
(get-model)
