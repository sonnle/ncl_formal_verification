(set-logic QF_BV)

; Inputs X:
(declare-fun X0 () (_ BitVec 2))
(declare-fun X0_d () (_ BitVec 2))
(declare-fun X1 () (_ BitVec 2))
(declare-fun X1_d () (_ BitVec 2))
(declare-fun X2 () (_ BitVec 2))
(declare-fun X2_d () (_ BitVec 2))

; Inputs Y:
(declare-fun Y0 () (_ BitVec 2))
(declare-fun Y0_d () (_ BitVec 2))
(declare-fun Y1 () (_ BitVec 2))
(declare-fun Y1_d () (_ BitVec 2))
(declare-fun Y2 () (_ BitVec 2))
(declare-fun Y2_d () (_ BitVec 2))

; Outputs Z:
(declare-fun Z0 () (_ BitVec 2))
(declare-fun Z1 () (_ BitVec 2))
(declare-fun Z2 () (_ BitVec 2))
(declare-fun Z3 () (_ BitVec 2))
(declare-fun Z4 () (_ BitVec 2))
(declare-fun Z5 () (_ BitVec 2))

; Current Theshold Gate Values:
(declare-fun Gc_0 () (_ BitVec 1))

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
    (= (_ bv0 2) a)
)

; Determine if the dual rail signal is data (0b01 OR 0b10)
(define-fun datap ((a (_ BitVec 2))) (Bool)
    (or
        (= (_ bv1 2) a)
        (= (_ bv2 2) a)
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
(define-fun and2 ((a (_ BitVec 2)) (b (_ BitVec 2)) (gl_1 (_ BitVec 1)) (gl_0 (_ BitVec 1))) (_ BitVec 2)
    (concat (th22 (rail1 a) (rail1 b) gl_1) (thand0 (rail0 b) (rail0 a) (rail1 b) (rail1 a) gl_0))
)

; NCL Half-Adder
; The output will be concatenated as follows:        | variable - S1, S0, Cout1, Cout0
;                                                    |      bit -  3,  2,     1,     0
; The last gate values (gl) will be used as follows: | variable -      gl_3,      gl_2, gl_1, gl_0
;                                                    |     gate - th24comp0, th24comp1, th12, th22
; TODO: Make the inputs individual rails so that we can mismash the inputs
(define-fun ha ((x (_ BitVec 2)) (y (_ BitVec 2)) (gl_3 (_ BitVec 1)) (gl_2 (_ BitVec 1)) (gl_1 (_ BitVec 1)) (gl_0 (_ BitVec 1))) (_ BitVec 4)
    (concat
        (th24comp (rail0 y) (rail0 x) (rail1 y) (rail1 x) gl_3)
        (th24comp (rail0 y) (rail1 x) (rail0 x) (rail1 y) gl_2)
        (th22 (rail1 y) (rail1 x) gl_1)
        (th12 (rail0 y) (rail0 x) gl_0))
)

; NCL Full-Adder
; The output will be concatenated as follows:        | variable - S1, S0, Cout1, Cout0
;                                                    |      bit -  3,  2,     1,     0
; The last gate values (gl) will be used as follows: | variable -        gl_3,        gl_2,         gl_1,         gl_0
;                                                    |     gate - th23 rail 0, th23 rail 1, th35w2 rail0, th35w2 rail1
; TODO: Make the inputs individual rails so that we can mismash the inputs
(define-fun fa ((x (_ BitVec 2)) (y (_ BitVec 2)) (cin (_ BitVec 2)) (gl_3 (_ BitVec 1)) (gl_2 (_ BitVec 1)) (gl_1 (_ BitVec 1)) (gl_0 (_ BitVec 1))) (_ BitVec 4)
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
                (and0x0 (and2 X0 Y0 Gc_0 Gc_0))
                (and0x1 (and2 X0 Y1 Gc_0 Gc_0))
                (and0x2 (and2 X0 Y2 Gc_0 Gc_0))
                (and1x0 (and2 X1 Y0 Gc_0 Gc_0))
                (and1x1 (and2 X1 Y1 Gc_0 Gc_0))
                (and1x2 (and2 X1 Y2 Gc_0 Gc_0))
                (and2x0 (and2 X2 Y0 Gc_0 Gc_0))
                (and2x1 (and2 X2 Y1 Gc_0 Gc_0))
                (and2x2 (and2 X2 Y2 Gc_0 Gc_0)))
        (let
            (
                (S0x0 and0x0))
        (let
            (
                (S1x1 ((_ extract 3 2) (ha and1x0 and0x1 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C1x1 ((_ extract 1 0) (ha and1x0 and0x1 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (S1x2 ((_ extract 3 2) (fa and2x0 and1x1 C1x1 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C1x2 ((_ extract 1 0) (fa and2x0 and1x1 C1x1 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (S2x2 ((_ extract 3 2) (ha and0x2 S1x2 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C2x2 ((_ extract 1 0) (ha and0x2 S1x2 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (S2x3 ((_ extract 3 2) (fa and2x1 C1x2 C2x2 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C2x3 ((_ extract 1 0) (fa and2x1 C1x2 C2x2 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (S3x3 ((_ extract 3 2) (ha and1x2 S2x3 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C3x3 ((_ extract 1 0) (ha and1x2 S2x3 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (S3x4 ((_ extract 3 2) (fa and2x2 C2x3 C3x3 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C3x4 ((_ extract 1 0) (fa and2x2 C2x3 C3x3 Gc_0 Gc_0 Gc_0 Gc_0))))
        (let
            (
                (and0x0_d (and2 X0_d Y0_d (rail1 and0x0) (rail0 and0x0)))
                (and0x1_d (and2 X0_d Y1_d (rail1 and0x1) (rail0 and0x1)))
                (and0x2_d (and2 X0_d Y2_d (rail1 and0x2) (rail0 and0x2)))
                (and1x0_d (and2 X1_d Y0_d (rail1 and1x0) (rail0 and1x0)))
                (and1x1_d (and2 X1_d Y1_d (rail1 and1x1) (rail0 and1x1)))
                (and1x2_d (and2 X1_d Y2_d (rail1 and1x2) (rail0 and1x2)))
                (and2x0_d (and2 X2_d Y0_d (rail1 and2x0) (rail0 and2x0)))
                (and2x1_d (and2 X2_d Y1_d (rail1 and2x1) (rail0 and2x1)))
                (and2x2_d (and2 X2_d Y2_d (rail1 and2x2) (rail0 and2x2))))
        (let
            (
                (S0x0_d and0x0_d))
        (let
            (
                (S1x1_d ((_ extract 3 2) (ha and1x0_d and0x1_d (rail1 S1x1) (rail0 S1x1) (rail1 C1x1) (rail0 C1x1))))
                (C1x1_d ((_ extract 1 0) (ha and1x0_d and0x1_d (rail1 S1x1) (rail0 S1x1) (rail1 C1x1) (rail0 C1x1)))))
        (let
            (
                (S1x2_d ((_ extract 3 2) (fa and2x0_d and1x1_d C1x1_d (rail1 S1x2) (rail0 S1x2) (rail1 C1x2) (rail0 C1x2))))
                (C1x2_d ((_ extract 1 0) (fa and2x0_d and1x1_d C1x1_d (rail1 S1x2) (rail0 S1x2) (rail1 C1x2) (rail0 C1x2)))))
        (let
            (
                (S2x2_d ((_ extract 3 2) (ha and0x2_d S1x2_d (rail1 S2x2) (rail0 S2x2) (rail1 C2x2) (rail0 C2x2))))
                (C2x2_d ((_ extract 1 0) (ha and0x2_d S1x2_d (rail1 S2x2) (rail0 S2x2) (rail1 C2x2) (rail0 C2x2)))))
        (let
            (
                (S2x3_d ((_ extract 3 2) (fa and2x1_d C1x2_d C2x2_d (rail1 S2x3) (rail0 S2x3) (rail1 C2x3) (rail0 C2x3))))
                (C2x3_d ((_ extract 1 0) (fa and2x1_d C1x2_d C2x2_d (rail1 S2x3) (rail0 S2x3) (rail1 C2x3) (rail0 C2x3)))))
        (let
            (
                (S3x3_d ((_ extract 3 2) (ha and1x2_d S2x3_d (rail1 S3x3) (rail0 S3x3) (rail1 C3x3) (rail0 C3x3))))
                (C3x3_d ((_ extract 1 0) (ha and1x2_d S2x3_d (rail1 S3x3) (rail0 S3x3) (rail1 C3x3) (rail0 C3x3)))))
        (let
            (
                (S3x4_d ((_ extract 3 2) (fa and2x2_d C2x3_d C3x3_d (rail1 S3x4) (rail0 S3x4) (rail1 C3x4) (rail0 C3x4))))
                (C3x4_d ((_ extract 1 0) (fa and2x2_d C2x3_d C3x3_d (rail1 S3x4) (rail0 S3x4) (rail1 C3x4) (rail0 C3x4)))))
        (let
            (
                (Z0 S0x0_d)
                (Z1 S1x1_d)
                (Z2 S2x2_d)
                (Z3 S3x3_d)
                (Z4 S3x4_d)
                (Z5 C3x4_d))
        (=>
            (and
                (= (_ bv0 1) Gc_0)
                (datap X0)
                (datap Y0)
                (datap X1)
                (datap Y1)
                (datap X2)
                (datap Y2)
                (not (= (_ bv3 2) X0_d))
                (not (= (_ bv3 2) Y0_d))
                (not (= (_ bv3 2) X1_d))
                (not (= (_ bv3 2) Y1_d))
                (not (= (_ bv3 2) X2_d))
                (not (= (_ bv3 2) Y2_d))
                (or
                    (nullp X0_d)
                    (= X0 X0_d))
                (or
                    (nullp X1_d)
                    (= X1 X1_d))
                (or
                    (nullp X2_d)
                    (= X2 X2_d))
                (or
                    (nullp Y0_d)
                    (= Y0 Y0_d))
                (or
                    (nullp Y1_d)
                    (= Y1 Y1_d))
                (or
                    (nullp Y2_d)
                    (= Y2 Y2_d))
                (or
                    (datap X0_d)
                    (datap Y0_d)
                    (datap X1_d)
                    (datap Y1_d)
                    (datap X2_d)
                    (datap Y2_d)))
        (or
            (datap Z0)
            (datap Z1)
            (datap Z2)
            (datap Z3)
            (datap Z4)
            (datap Z5))))))))))))))))))))
    )
)

(check-sat)
(get-model)

