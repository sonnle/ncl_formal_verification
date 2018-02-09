; Formal verification proof - input completeness of ..\netlist_files\unsigned_mult_3x3.txt
(set-logic QF_BV)

; Inputs: X0, X1, X2, Y0, Y1, Y2
(declare-fun X0 () (_ BitVec 2))
(declare-fun X1 () (_ BitVec 2))
(declare-fun X2 () (_ BitVec 2))
(declare-fun Y0 () (_ BitVec 2))
(declare-fun Y1 () (_ BitVec 2))
(declare-fun Y2 () (_ BitVec 2))

; Outputs: Z0, Z1, Z2, Z3, Z4, Z5
(declare-fun Z0 () (_ BitVec 2))
(declare-fun Z1 () (_ BitVec 2))
(declare-fun Z2 () (_ BitVec 2))
(declare-fun Z3 () (_ BitVec 2))
(declare-fun Z4 () (_ BitVec 2))
(declare-fun Z5 () (_ BitVec 2))

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

; Current values of threshold gates
(declare-fun Gc_0 () (_ BitVec 1))
(declare-fun Gc_1 () (_ BitVec 1))
(declare-fun Gc_2 () (_ BitVec 1))
(declare-fun Gc_3 () (_ BitVec 1))
(declare-fun Gc_4 () (_ BitVec 1))
(declare-fun Gc_5 () (_ BitVec 1))
(declare-fun Gc_6 () (_ BitVec 1))
(declare-fun Gc_7 () (_ BitVec 1))
(declare-fun Gc_8 () (_ BitVec 1))
(declare-fun Gc_9 () (_ BitVec 1))
(declare-fun Gc_10 () (_ BitVec 1))
(declare-fun Gc_11 () (_ BitVec 1))
(declare-fun Gc_12 () (_ BitVec 1))
(declare-fun Gc_13 () (_ BitVec 1))
(declare-fun Gc_14 () (_ BitVec 1))
(declare-fun Gc_15 () (_ BitVec 1))
(declare-fun Gc_16 () (_ BitVec 1))
(declare-fun Gc_17 () (_ BitVec 1))
(declare-fun Gc_18 () (_ BitVec 1))
(declare-fun Gc_19 () (_ BitVec 1))
(declare-fun Gc_20 () (_ BitVec 1))
(declare-fun Gc_21 () (_ BitVec 1))
(declare-fun Gc_22 () (_ BitVec 1))
(declare-fun Gc_23 () (_ BitVec 1))
(declare-fun Gc_24 () (_ BitVec 1))
(declare-fun Gc_25 () (_ BitVec 1))
(declare-fun Gc_26 () (_ BitVec 1))
(declare-fun Gc_27 () (_ BitVec 1))
(declare-fun Gc_28 () (_ BitVec 1))
(declare-fun Gc_29 () (_ BitVec 1))
(declare-fun Gc_30 () (_ BitVec 1))
(declare-fun Gc_31 () (_ BitVec 1))
(declare-fun Gc_32 () (_ BitVec 1))
(declare-fun Gc_33 () (_ BitVec 1))
(declare-fun Gc_34 () (_ BitVec 1))
(declare-fun Gc_35 () (_ BitVec 1))
(declare-fun Gc_36 () (_ BitVec 1))
(declare-fun Gc_37 () (_ BitVec 1))
(declare-fun Gc_38 () (_ BitVec 1))
(declare-fun Gc_39 () (_ BitVec 1))
(declare-fun Gc_40 () (_ BitVec 1))
(declare-fun Gc_41 () (_ BitVec 1))

; SAT/UNSAT assertion for ..\netlist_files\unsigned_mult_3x3.txt
(assert
    (not
        (let
            (
                (I0 (and2 X0 Y0 Gc_0 Gc_1))
                (I1 (and2 X1 Y0 Gc_2 Gc_3))
                (I2 (and2 X0 Y1 Gc_4 Gc_5))
                (I3 (and2 X2 Y0 Gc_6 Gc_7))
                (I4 (and2 X1 Y1 Gc_8 Gc_9))
                (I5 (and2 X2 Y1 Gc_10 Gc_11))
                (I6 (and2 X2 Y2 Gc_12 Gc_13))
                (I7 (and2 X0 Y2 Gc_14 Gc_15))
                (I8 (and2 X1 Y2 Gc_16 Gc_17))
            )
        (let
            (
                (I9 ((_ extract 3 2) (ha I1 I2 Gc_18 Gc_19 Gc_20 Gc_21)))
                (I10 ((_ extract 1 0) (ha I1 I2 Gc_18 Gc_19 Gc_20 Gc_21)))
            )
        (let
            (
                (I11 ((_ extract 3 2) (fa I3 I4 I10 Gc_22 Gc_23 Gc_24 Gc_25)))
                (I12 ((_ extract 1 0) (fa I3 I4 I10 Gc_22 Gc_23 Gc_24 Gc_25)))
            )
        (let
            (
                (I13 ((_ extract 3 2) (ha I7 I11 Gc_26 Gc_27 Gc_28 Gc_29)))
                (I14 ((_ extract 1 0) (ha I7 I11 Gc_26 Gc_27 Gc_28 Gc_29)))
            )
        (let
            (
                (I15 ((_ extract 3 2) (fa I5 I12 I14 Gc_30 Gc_31 Gc_32 Gc_33)))
                (I16 ((_ extract 1 0) (fa I5 I12 I14 Gc_30 Gc_31 Gc_32 Gc_33)))
            )
        (let
            (
                (I17 ((_ extract 3 2) (ha I8 I15 Gc_34 Gc_35 Gc_36 Gc_37)))
                (I18 ((_ extract 1 0) (ha I8 I15 Gc_34 Gc_35 Gc_36 Gc_37)))
            )
        (let
            (
                (I19 ((_ extract 3 2) (fa I6 I16 I18 Gc_38 Gc_39 Gc_40 Gc_41)))
                (I20 ((_ extract 1 0) (fa I6 I16 I18 Gc_38 Gc_39 Gc_40 Gc_41)))
            )
        (let
            (
                (Z0 I0)
                (Z1 I9)
                (Z2 I13)
                (Z3 I17)
                (Z4 I19)
                (Z5 I20)
            )
        (=>
            (and
                (not (= (_ bv3 2) X0))
                (not (= (_ bv3 2) X1))
                (not (= (_ bv3 2) X2))
                (not (= (_ bv3 2) Y0))
                (not (= (_ bv3 2) Y1))
                (not (= (_ bv3 2) Y2))
                (= (_ bv0 1) Gc_0)
                (= (_ bv0 1) Gc_1)
                (= (_ bv0 1) Gc_2)
                (= (_ bv0 1) Gc_3)
                (= (_ bv0 1) Gc_4)
                (= (_ bv0 1) Gc_5)
                (= (_ bv0 1) Gc_6)
                (= (_ bv0 1) Gc_7)
                (= (_ bv0 1) Gc_8)
                (= (_ bv0 1) Gc_9)
                (= (_ bv0 1) Gc_10)
                (= (_ bv0 1) Gc_11)
                (= (_ bv0 1) Gc_12)
                (= (_ bv0 1) Gc_13)
                (= (_ bv0 1) Gc_14)
                (= (_ bv0 1) Gc_15)
                (= (_ bv0 1) Gc_16)
                (= (_ bv0 1) Gc_17)
                (= (_ bv0 1) Gc_18)
                (= (_ bv0 1) Gc_19)
                (= (_ bv0 1) Gc_20)
                (= (_ bv0 1) Gc_21)
                (= (_ bv0 1) Gc_22)
                (= (_ bv0 1) Gc_23)
                (= (_ bv0 1) Gc_24)
                (= (_ bv0 1) Gc_25)
                (= (_ bv0 1) Gc_26)
                (= (_ bv0 1) Gc_27)
                (= (_ bv0 1) Gc_28)
                (= (_ bv0 1) Gc_29)
                (= (_ bv0 1) Gc_30)
                (= (_ bv0 1) Gc_31)
                (= (_ bv0 1) Gc_32)
                (= (_ bv0 1) Gc_33)
                (= (_ bv0 1) Gc_34)
                (= (_ bv0 1) Gc_35)
                (= (_ bv0 1) Gc_36)
                (= (_ bv0 1) Gc_37)
                (= (_ bv0 1) Gc_38)
                (= (_ bv0 1) Gc_39)
                (= (_ bv0 1) Gc_40)
                (= (_ bv0 1) Gc_41)
                (or
                    (nullp X0)
                    (nullp X1)
                    (nullp X2)
                    (nullp Y0)
                    (nullp Y1)
                    (nullp Y2)))
            (or
                (nullp Z0)
                (nullp Z1)
                (nullp Z2)
                (nullp Z3)
                (nullp Z4)
                (nullp Z5)))))))))))
    )
)

(check-sat)
(get-model)
