(set-logic QF_BV)

; Inputs
(declare-fun X     () (_ BitVec 2))
(declare-fun Y     () (_ BitVec 2))
(declare-fun Cin   () (_ BitVec 2))

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

; NCL Gate Boolean Function - TH23: (AB + AC + BC)
(define-fun th23 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
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
                	(bvand a c)
                    (bvand b c)))
            (_ bv1 1)
            gl))
)

; NCL Gate Boolean Function - TH34w2: (AB + AC + AD + BCD)
(define-fun th34w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
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
            gl))
)

; NCL Full-Adder
; The output will be concatenated as follows:        | variable - S1, S0, Cout1, Cout0
;                                                    |      bit -  3,  2,     1,     0
; The last gate values (gl) will be used as follows: | variable -        gl_0,        gl_1,         gl_2,         gl_3
;                                                    |     gate - th23 rail 0, th23 rail 1, th35w2 rail0, th35w2 rail1
(define-fun FA ((x (_ BitVec 2)) (y (_ BitVec 2)) (cin (_ BitVec 2)) (gl_0 (_ BitVec 1)) (gl_1 (_ BitVec 1)) (gl_2 (_ BitVec 1)) (gl_3 (_ BitVec 1))) (_ BitVec 4)
    (let
        (
            (gn_0 (th23 (rail0 x) (rail0 y) (rail0 cin) gl_0))
            (gn_1 (th23 (rail1 x) (rail1 y) (rail1 cin) gl_1))
        )
    (let
        (
            (gn_2 (th34w2 gn_1 (rail0 x) (rail0 y) (rail0 cin) gl_2))
            (gn_3 (th34w2 gn_0 (rail1 x) (rail1 y) (rail1 cin) gl_3))
        )
    (concat gn_3 gn_2 gn_1 gn_0)))
)

(assert
    (not
        (let
            (
                (result (FA X Y Cin Gc_0 Gc_1 Gc_2 Gc_3))
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
                (not (= Cin (_ bv0 2)))
                (not (= X (_ bv3 2)))
                (not (= Y (_ bv3 2)))
                (not (= Cin (_ bv3 2)))
            )
            (= ((_ extract 3 3) result) (bvadd (rail1 X) (rail1 Y) (rail1 Cin)))))
    )
)

(check-sat)
(get-model)
