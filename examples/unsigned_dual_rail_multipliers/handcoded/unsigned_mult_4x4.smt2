; Formal verification proof - input completeness of ..\netlist_files\unsigned_mult_4x4.txt
(set-logic QF_BV)

; Inputs: X0, X1, X2, X3, Y0, Y1, Y2, Y3
(declare-fun X0 () (_ BitVec 2))
(declare-fun X1 () (_ BitVec 2))
(declare-fun X2 () (_ BitVec 2))
(declare-fun X3 () (_ BitVec 2))
(declare-fun Y0 () (_ BitVec 2))
(declare-fun Y1 () (_ BitVec 2))
(declare-fun Y2 () (_ BitVec 2))
(declare-fun Y3 () (_ BitVec 2))

; Outputs: Z0, Z1, Z2, Z3, Z4, Z5, Z6, Z7
(declare-fun Z0 () (_ BitVec 2))
(declare-fun Z1 () (_ BitVec 2))
(declare-fun Z2 () (_ BitVec 2))
(declare-fun Z3 () (_ BitVec 2))
(declare-fun Z4 () (_ BitVec 2))
(declare-fun Z5 () (_ BitVec 2))
(declare-fun Z6 () (_ BitVec 2))
(declare-fun Z7 () (_ BitVec 2))

; Extract rail0 of a dual rail signal
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 0 0) a)
)

; Extract rail1 of a dual rail signal
(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 1 1) a)
)

; Determine if the dual rail signal is null (0b00)
(define-fun nullp ((a (_ BitVec 2))) (Bool)
    (and
        (= (_ bv0 1) (rail0 a))
        (= (_ bv0 1) (rail1 a))
    )
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

; NCL Gate Boolean Function - THand0: (AB + BC + AD)
(define-fun thand0 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
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
            gl))
)

; NCL Gate Dual Rail AND Logic
(define-fun and2 ((a (_ BitVec 2)) (b (_ BitVec 2)) (gl_0 (_ BitVec 1)) (gl_1 (_ BitVec 1))) (_ BitVec 2)
    (concat (th22 (rail1 a) (rail1 b) gl_0) (thand0 (rail0 b) (rail0 a) (rail1 b) (rail1 a) gl_1))
)

; NCL Half-Adder
; The output will be concatenated as follows:        | variable - S1, S0, Cout1, Cout0
;                                                    |      bit -  3,  2,     1,     0
; The last gate values (gl) will be used as follows: | variable -      gl_0,      gl_1, gl_2, gl_3
;                                                    |     gate - th24comp0, th24comp1, th12, th22
; TODO: Make the inputs individual rails so that we can mismash the inputs
(define-fun ha ((x (_ BitVec 2)) (y (_ BitVec 2)) (gl_0 (_ BitVec 1)) (gl_1 (_ BitVec 1)) (gl_2 (_ BitVec 1)) (gl_3 (_ BitVec 1))) (_ BitVec 4)
    (concat
        (th24comp (rail0 y) (rail0 x) (rail1 y) (rail1 x) gl_1)
        (th24comp (rail0 y) (rail1 x) (rail0 x) (rail1 y) gl_0)
        (th22 (rail1 y) (rail1 x) gl_3)
        (th12 (rail0 y) (rail0 x) gl_2))
)

; NCL Full-Adder
; The output will be concatenated as follows:        | variable - S1, S0, Cout1, Cout0
;                                                    |      bit -  3,  2,     1,     0
; The last gate values (gl) will be used as follows: | variable -        gl_0,        gl_1,         gl_2,         gl_3
;                                                    |     gate - th23 rail 0, th23 rail 1, th35w2 rail0, th35w2 rail1
; TODO: Make the inputs individual rails so that we can mismash the inputs

(define-fun fa ((x (_ BitVec 2)) (y (_ BitVec 2)) (cin (_ BitVec 2)) (gl_0 (_ BitVec 1)) (gl_1 (_ BitVec 1)) (gl_2 (_ BitVec 1)) (gl_3 (_ BitVec 1))) (_ BitVec 4)
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

; Current values of threshold gates
(declare-fun Gc_0 () (_ BitVec 1))

; SAT/UNSAT assertion for ..\netlist_files\unsigned_mult_4x4.txt
(assert
    (not
        (let
            (
                (I0 (and2 X0 Y0 Gc_0 Gc_0))
                (I1 (and2 X0 Y1 Gc_0 Gc_0))
                (I2 (and2 X1 Y0 Gc_0 Gc_0))
                (I3 (and2 X0 Y2 Gc_0 Gc_0))
                (I4 (and2 X1 Y1 Gc_0 Gc_0))
                (I5 (and2 X2 Y0 Gc_0 Gc_0))
                (I6 (and2 X0 Y3 Gc_0 Gc_0))
                (I7 (and2 X1 Y2 Gc_0 Gc_0))
                (I8 (and2 X2 Y1 Gc_0 Gc_0))
                (I9 (and2 X3 Y0 Gc_0 Gc_0))
                (I10 (and2 X1 Y3 Gc_0 Gc_0))
                (I11 (and2 X2 Y2 Gc_0 Gc_0))
                (I12 (and2 X3 Y1 Gc_0 Gc_0))
                (I13 (and2 X2 Y3 Gc_0 Gc_0))
                (I14 (and2 X3 Y2 Gc_0 Gc_0))
                (I15 (and2 X3 Y3 Gc_0 Gc_0)))
        (let
            (
                (I16 ((_ extract 3 2) (ha I1 I2 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I17 ((_ extract 1 0) (ha I1 I2 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I18 ((_ extract 3 2) (fa I3 I4 I17 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I19 ((_ extract 1 0) (fa I3 I4 I17 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I20 ((_ extract 3 2) (fa I6 I7 I19 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I21 ((_ extract 1 0) (fa I6 I7 I19 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I22 ((_ extract 3 2) (ha I5 I18 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I23 ((_ extract 1 0) (ha I5 I18 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I24 ((_ extract 3 2) (fa I8 I20 I23 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I25 ((_ extract 1 0) (fa I8 I20 I23 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I26 ((_ extract 3 2) (fa I10 I21 I25 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I27 ((_ extract 1 0) (fa I10 I21 I25 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I28 ((_ extract 3 2) (ha I9 I24 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I29 ((_ extract 1 0) (ha I9 I24 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I30 ((_ extract 3 2) (fa I11 I26 I29 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I31 ((_ extract 1 0) (fa I11 I26 I29 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I32 ((_ extract 3 2) (fa I13 I27 I31 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I33 ((_ extract 1 0) (fa I13 I27 I31 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I34 ((_ extract 3 2) (ha I12 I30 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I35 ((_ extract 1 0) (ha I12 I30 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I36 ((_ extract 3 2) (fa I14 I32 I35 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I37 ((_ extract 1 0) (fa I14 I32 I35 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I38 ((_ extract 3 2) (fa I15 I33 I37 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I39 ((_ extract 1 0) (fa I15 I33 I37 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (Z0 I0)
                (Z1 I16)
                (Z2 I22)
                (Z3 I28)
                (Z4 I34)
                (Z5 I36)
                (Z6 I38)
                (Z7 I39))
        (=>
            (and
                (not (= (_ bv3 2) X0))
                (not (= (_ bv3 2) X1))
                (not (= (_ bv3 2) X2))
                (not (= (_ bv3 2) X3))
                (not (= (_ bv3 2) Y0))
                (not (= (_ bv3 2) Y1))
                (not (= (_ bv3 2) Y2))
                (not (= (_ bv3 2) Y3))
                (= (_ bv0 1) Gc_0)
                (or
                    (nullp X0)
                    (nullp X1)
                    (nullp X2)
                    (nullp X3)
                    (nullp Y0)
                    (nullp Y1)
                    (nullp Y2)
                    (nullp Y3)))
            (or
                (nullp Z0)
                (nullp Z1)
                (nullp Z2)
                (nullp Z3)
                (nullp Z4)
                (nullp Z5)
                (nullp Z6)
                (nullp Z7)))))))))))))))))
    )
)

(check-sat)
(get-model)
