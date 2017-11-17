(set-logic QF_BV)

; Inputs
(declare-fun X     () (_ BitVec 2))
(declare-fun Y     () (_ BitVec 2))

; Inputs
(declare-fun S     () (_ BitVec 2))
(declare-fun Cout     () (_ BitVec 2))

; Current gate values
(declare-fun Gc_0 () (_ BitVec 1))
(declare-fun Gc_1 () (_ BitVec 1))
(declare-fun Gc_2 () (_ BitVec 1))
(declare-fun Gc_3 () (_ BitVec 1))

; Extract rail0 of a dual rail signal
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 0 0) a)
)

; Extract rail1 of a dual rail signal
(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 1 1) a)
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

; NCL Gate Boolean Function - TH24comp: (AC + BC + AD + BD)
(define-fun th24comp ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
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
            gl))
)

; NCL Half-Adder
; The output will be concatenated as follows:        | variable - S1, S0, Cout1, Cout0
;                                                    |      bit -  3,  2,     1,     0
; The last gate values (gl) will be used as follows: | variable -      gl_0,      gl_1, gl_2, gl_3
;                                                    |     gate - th24comp0, th24comp1, th12, th22
(define-fun HA ((x (_ BitVec 2)) (y (_ BitVec 2)) (gl_0 (_ BitVec 1)) (gl_1 (_ BitVec 1)) (gl_2 (_ BitVec 1)) (gl_3 (_ BitVec 1))) (_ BitVec 4)
    (concat
        (th24comp (rail0 y) (rail0 x) (rail1 y) (rail1 x) gl_1)
        (th24comp (rail0 y) (rail1 x) (rail0 x) (rail1 y) gl_0)
        (th22 (rail1 y) (rail1 x) gl_3)
        (th12 (rail0 y) (rail0 x) gl_2))
)

(assert
    (not
        (let
            (
                (result (HA X Y Gc_0 Gc_1 Gc_2 Gc_3))
            )
        (=>
            (and
                (= S (concat ((_ extract 3 3) result) ((_ extract 2 2) result)))
                (= Cout (concat ((_ extract 1 1) result) ((_ extract 0 0) result)))
                (= Gc_0 (_ bv0 1))
                (= Gc_1 (_ bv0 1))
                (= Gc_2 (_ bv0 1))
                (= Gc_3 (_ bv0 1))
                (not (= X (_ bv0 2)))
                (not (= Y (_ bv0 2)))
                (not (= X (_ bv3 2)))
                (not (= Y (_ bv3 2)))
            )
            (= ((_ extract 3 3) result) (bvadd (rail1 X) (rail1 Y)))))
    )
)

(check-sat)
(get-model)
