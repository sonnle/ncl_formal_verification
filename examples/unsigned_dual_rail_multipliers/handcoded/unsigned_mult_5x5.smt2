; Formal verification proof - input completeness of ..\netlist_files\unsigned_mult_5x5.txt
(set-logic QF_BV)

; Inputs: X0, X1, X2, X3, X4, Y0, Y1, Y2, Y3, Y4
(declare-fun X0 () (_ BitVec 2))
(declare-fun X1 () (_ BitVec 2))
(declare-fun X2 () (_ BitVec 2))
(declare-fun X3 () (_ BitVec 2))
(declare-fun X4 () (_ BitVec 2))
(declare-fun Y0 () (_ BitVec 2))
(declare-fun Y1 () (_ BitVec 2))
(declare-fun Y2 () (_ BitVec 2))
(declare-fun Y3 () (_ BitVec 2))
(declare-fun Y4 () (_ BitVec 2))

; Outputs: Z0, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9
(declare-fun Z0 () (_ BitVec 2))
(declare-fun Z1 () (_ BitVec 2))
(declare-fun Z2 () (_ BitVec 2))
(declare-fun Z3 () (_ BitVec 2))
(declare-fun Z4 () (_ BitVec 2))
(declare-fun Z5 () (_ BitVec 2))
(declare-fun Z6 () (_ BitVec 2))
(declare-fun Z7 () (_ BitVec 2))
(declare-fun Z8 () (_ BitVec 2))
(declare-fun Z9 () (_ BitVec 2))

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

; SAT/UNSAT assertion for ..\netlist_files\unsigned_mult_5x5.txt
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
                (I10 (and2 X0 Y4 Gc_0 Gc_0))
                (I11 (and2 X1 Y3 Gc_0 Gc_0))
                (I12 (and2 X2 Y2 Gc_0 Gc_0))
                (I13 (and2 X3 Y1 Gc_0 Gc_0))
                (I14 (and2 X4 Y0 Gc_0 Gc_0))
                (I15 (and2 X1 Y4 Gc_0 Gc_0))
                (I16 (and2 X2 Y3 Gc_0 Gc_0))
                (I17 (and2 X3 Y2 Gc_0 Gc_0))
                (I18 (and2 X4 Y1 Gc_0 Gc_0))
                (I19 (and2 X2 Y4 Gc_0 Gc_0))
                (I20 (and2 X3 Y3 Gc_0 Gc_0))
                (I21 (and2 X4 Y2 Gc_0 Gc_0))
                (I22 (and2 X3 Y4 Gc_0 Gc_0))
                (I23 (and2 X4 Y3 Gc_0 Gc_0))
                (I24 (and2 X4 Y4 Gc_0 Gc_0)))
        (let
            (
                (I25 ((_ extract 3 2) (ha I1 I2 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I26 ((_ extract 1 0) (ha I1 I2 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I27 ((_ extract 3 2) (fa I3 I4 I26 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I28 ((_ extract 1 0) (fa I3 I4 I26 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I29 ((_ extract 3 2) (fa I6 I7 I28 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I30 ((_ extract 1 0) (fa I6 I7 I28 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I31 ((_ extract 3 2) (fa I10 I11 I30 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I32 ((_ extract 1 0) (fa I10 I11 I30 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I33 ((_ extract 3 2) (ha I5 I27 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I34 ((_ extract 1 0) (ha I5 I27 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I35 ((_ extract 3 2) (fa I8 I29 I34 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I36 ((_ extract 1 0) (fa I8 I29 I34 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I37 ((_ extract 3 2) (fa I12 I31 I36 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I38 ((_ extract 1 0) (fa I12 I31 I36 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I39 ((_ extract 3 2) (fa I15 I32 I38 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I40 ((_ extract 1 0) (fa I15 I32 I38 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I41 ((_ extract 3 2) (ha I9 I35 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I42 ((_ extract 1 0) (ha I9 I35 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I43 ((_ extract 3 2) (fa I13 I37 I42 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I44 ((_ extract 1 0) (fa I13 I37 I42 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I45 ((_ extract 3 2) (fa I16 I39 I44 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I46 ((_ extract 1 0) (fa I16 I39 I44 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I47 ((_ extract 3 2) (fa I19 I40 I46 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I48 ((_ extract 1 0) (fa I19 I40 I46 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I49 ((_ extract 3 2) (ha I14 I43 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I50 ((_ extract 1 0) (ha I14 I43 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I51 ((_ extract 3 2) (fa I17 I45 I50 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I52 ((_ extract 1 0) (fa I17 I45 I50 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I53 ((_ extract 3 2) (fa I20 I47 I51 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I54 ((_ extract 1 0) (fa I20 I47 I51 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I55 ((_ extract 3 2) (fa I22 I48 I54 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I56 ((_ extract 1 0) (fa I22 I48 I54 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I57 ((_ extract 3 2) (ha I18 I51 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I58 ((_ extract 1 0) (ha I18 I51 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I59 ((_ extract 3 2) (fa I21 I53 I58 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I60 ((_ extract 1 0) (fa I21 I53 I58 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I61 ((_ extract 3 2) (fa I23 I55 I60 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I62 ((_ extract 1 0) (fa I23 I55 I60 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (I63 ((_ extract 3 2) (fa I24 I56 I62 Gc_0 Gc_0 Gc_0 Gc_0)))
                (I64 ((_ extract 1 0) (fa I24 I56 I62 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (Z0 I0)
                (Z1 I25)
                (Z2 I3)
                (Z3 I41)
                (Z4 I49)
                (Z5 I57)
                (Z6 I59)
                (Z7 I61)
                (Z8 I63)
                (Z9 I64))
        (=>
            (and
                (not (= (_ bv3 2) X0))
                (not (= (_ bv3 2) X1))
                (not (= (_ bv3 2) X2))
                (not (= (_ bv3 2) X3))
                (not (= (_ bv3 2) X4))
                (not (= (_ bv3 2) Y0))
                (not (= (_ bv3 2) Y1))
                (not (= (_ bv3 2) Y2))
                (not (= (_ bv3 2) Y3))
                (not (= (_ bv3 2) Y4))
                (= (_ bv0 1) Gc_0)
                (or
                    (nullp X0)
                    (nullp X1)
                    (nullp X2)
                    (nullp X3)
                    (nullp X4)
                    (nullp Y0)
                    (nullp Y1)
                    (nullp Y2)
                    (nullp Y3)
                    (nullp Y4)))
            (or
                (nullp Z0)
                (nullp Z1)
                (nullp Z2)
                (nullp Z3)
                (nullp Z4)
                (nullp Z5)
                (nullp Z6)
                (nullp Z7)
                (nullp Z8)))))))))))))))))))))))))
    )
)

(check-sat)
(get-model)
