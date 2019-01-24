(set-logic QF_BV)
; Inputs: X0 X1 X2 X3 X4 X5 X6 X7 Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7
(declare-fun X0 () (_ BitVec 2))
(declare-fun X1 () (_ BitVec 2))
(declare-fun X2 () (_ BitVec 2))
(declare-fun X3 () (_ BitVec 2))
(declare-fun X4 () (_ BitVec 2))
(declare-fun X5 () (_ BitVec 2))
(declare-fun X6 () (_ BitVec 2))
(declare-fun X7 () (_ BitVec 2))
(declare-fun Y0 () (_ BitVec 2))
(declare-fun Y1 () (_ BitVec 2))
(declare-fun Y2 () (_ BitVec 2))
(declare-fun Y3 () (_ BitVec 2))
(declare-fun Y4 () (_ BitVec 2))
(declare-fun Y5 () (_ BitVec 2))
(declare-fun Y6 () (_ BitVec 2))
(declare-fun Y7 () (_ BitVec 2))
; Outputs: Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7 Z8 Z9 Z10 Z11 Z12 Z13 Z14 Z15
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
(declare-fun Z10 () (_ BitVec 2))
(declare-fun Z11 () (_ BitVec 2))
(declare-fun Z12 () (_ BitVec 2))
(declare-fun Z13 () (_ BitVec 2))
(declare-fun Z14 () (_ BitVec 2))
(declare-fun Z15 () (_ BitVec 2))
; Current gate outputs
(declare-fun Gc_0 () (_ BitVec 1))
; Determine if the dual rail signal is null (0b00)
(define-fun nullp ((a (_ BitVec 2))) (Bool)
    (= (_ bv0 2) a)
)
; Extract rail0 of a dual rail signal
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 0 0) a)
)

; Extract rail1 of a dual rail signal
(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 1 1) a)
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
(assert
(not
(let
(
(and2x5_1 (th22 (rail1 X2) (rail1 Y5) Gc_0))
(and2x5_0 (th12 (rail0 X2) (rail0 Y5) Gc_0))
(and0x5_1 (th22 (rail1 X0) (rail1 Y5) Gc_0))
(and0x5_0 (th12 (rail0 X0) (rail0 Y5) Gc_0))
(and2x3_1 (th22 (rail1 X2) (rail1 Y3) Gc_0))
(and2x3_0 (th12 (rail0 X2) (rail0 Y3) Gc_0))
(and7x1_0 (th12 (rail0 X7) (rail0 Y1) Gc_0))
(and7x1_1 (th22 (rail1 X7) (rail1 Y1) Gc_0))
(and2x1_1 (th22 (rail1 X2) (rail1 Y1) Gc_0))
(and2x1_0 (th12 (rail0 X2) (rail0 Y1) Gc_0))
(and0x7_1 (th22 (rail1 X0) (rail1 Y7) Gc_0))
(and0x7_0 (th12 (rail0 X0) (rail0 Y7) Gc_0))
(and5x2_1 (th22 (rail1 X5) (rail1 Y2) Gc_0))
(and5x2_0 (th12 (rail0 X5) (rail0 Y2) Gc_0))
(and4x4_0 (thand0 (rail0 Y4) (rail0 X4) (rail1 Y4) (rail1 X4) Gc_0))
(and4x4_1 (th22 (rail1 X4) (rail1 Y4) Gc_0))
(and3x4_1 (th22 (rail1 X3) (rail1 Y4) Gc_0))
(and3x4_0 (th12 (rail0 X3) (rail0 Y4) Gc_0))
(and4x6_0 (th12 (rail0 X4) (rail0 Y6) Gc_0))
(and4x6_1 (th22 (rail1 X4) (rail1 Y6) Gc_0))
(and6x1_1 (th22 (rail1 X6) (rail1 Y1) Gc_0))
(and6x1_0 (th12 (rail0 X6) (rail0 Y1) Gc_0))
(and4x0_0 (th12 (rail0 X4) (rail0 Y0) Gc_0))
(and4x0_1 (th22 (rail1 X4) (rail1 Y0) Gc_0))
(and2x7_1 (th22 (rail1 X2) (rail1 Y7) Gc_0))
(and2x7_0 (th12 (rail0 X2) (rail0 Y7) Gc_0))
(and4x2_0 (th12 (rail0 X4) (rail0 Y2) Gc_0))
(and4x2_1 (th22 (rail1 X4) (rail1 Y2) Gc_0))
(and1x4_1 (th22 (rail1 X1) (rail1 Y4) Gc_0))
(and1x4_0 (th12 (rail0 X1) (rail0 Y4) Gc_0))
(and0x2_0 (th12 (rail0 X0) (rail0 Y2) Gc_0))
(and0x2_1 (th22 (rail1 X0) (rail1 Y2) Gc_0))
(and2x4_0 (th12 (rail0 X2) (rail0 Y4) Gc_0))
(and2x4_1 (th22 (rail1 X2) (rail1 Y4) Gc_0))
(and0x4_0 (th12 (rail0 X0) (rail0 Y4) Gc_0))
(and0x4_1 (th22 (rail1 X0) (rail1 Y4) Gc_0))
(and6x7_1 (th22 (rail1 X6) (rail1 Y7) Gc_0))
(and6x7_0 (th12 (rail0 X6) (rail0 Y7) Gc_0))
(and1x6_1 (th22 (rail1 X1) (rail1 Y6) Gc_0))
(and1x6_0 (th12 (rail0 X1) (rail0 Y6) Gc_0))
(and6x5_1 (th22 (rail1 X6) (rail1 Y5) Gc_0))
(and6x5_0 (th12 (rail0 X6) (rail0 Y5) Gc_0))
(and0x6_0 (th12 (rail0 X0) (rail0 Y6) Gc_0))
(and0x6_1 (th22 (rail1 X0) (rail1 Y6) Gc_0))
(and6x3_1 (th22 (rail1 X6) (rail1 Y3) Gc_0))
(and6x3_0 (th12 (rail0 X6) (rail0 Y3) Gc_0))
(and6x2_0 (th12 (rail0 X6) (rail0 Y2) Gc_0))
(and6x2_1 (th22 (rail1 X6) (rail1 Y2) Gc_0))
(and5x6_1 (th22 (rail1 X5) (rail1 Y6) Gc_0))
(and5x6_0 (th12 (rail0 X5) (rail0 Y6) Gc_0))
(and4x7_1 (th22 (rail1 X4) (rail1 Y7) Gc_0))
(and4x7_0 (th12 (rail0 X4) (rail0 Y7) Gc_0))
(and5x0_1 (th22 (rail1 X5) (rail1 Y0) Gc_0))
(and5x0_0 (th12 (rail0 X5) (rail0 Y0) Gc_0))
(and4x1_1 (th22 (rail1 X4) (rail1 Y1) Gc_0))
(and4x1_0 (th12 (rail0 X4) (rail0 Y1) Gc_0))
(Z0_1 (th22 (rail1 X0) (rail1 Y0) Gc_0))
(Z0_0 (thand0 (rail0 Y0) (rail0 X0) (rail1 Y0) (rail1 X0) Gc_0))
(and6x0_0 (th12 (rail0 X6) (rail0 Y0) Gc_0))
(and6x0_1 (th22 (rail1 X6) (rail1 Y0) Gc_0))
(and2x0_0 (th12 (rail0 X2) (rail0 Y0) Gc_0))
(and2x0_1 (th22 (rail1 X2) (rail1 Y0) Gc_0))
(and1x0_1 (th22 (rail1 X1) (rail1 Y0) Gc_0))
(and1x0_0 (th12 (rail0 X1) (rail0 Y0) Gc_0))
(and2x6_0 (th12 (rail0 X2) (rail0 Y6) Gc_0))
(and2x6_1 (th22 (rail1 X2) (rail1 Y6) Gc_0))
(and1x2_1 (th22 (rail1 X1) (rail1 Y2) Gc_0))
(and1x2_0 (th12 (rail0 X1) (rail0 Y2) Gc_0))
(and4x3_1 (th22 (rail1 X4) (rail1 Y3) Gc_0))
(and4x3_0 (th12 (rail0 X4) (rail0 Y3) Gc_0))
(and1x5_0 (th12 (rail0 X1) (rail0 Y5) Gc_0))
(and1x5_1 (th22 (rail1 X1) (rail1 Y5) Gc_0))
(and7x6_1 (th22 (rail1 X7) (rail1 Y6) Gc_0))
(and7x6_0 (th12 (rail0 X7) (rail0 Y6) Gc_0))
(and7x4_1 (th22 (rail1 X7) (rail1 Y4) Gc_0))
(and7x4_0 (th12 (rail0 X7) (rail0 Y4) Gc_0))
(and6x6_0 (thand0 (rail0 Y6) (rail0 X6) (rail1 Y6) (rail1 X6) Gc_0))
(and6x6_1 (th22 (rail1 X6) (rail1 Y6) Gc_0))
(and1x7_0 (th12 (rail0 X1) (rail0 Y7) Gc_0))
(and1x7_1 (th22 (rail1 X1) (rail1 Y7) Gc_0))
(and7x2_1 (th22 (rail1 X7) (rail1 Y2) Gc_0))
(and7x2_0 (th12 (rail0 X7) (rail0 Y2) Gc_0))
(and6x4_0 (th12 (rail0 X6) (rail0 Y4) Gc_0))
(and6x4_1 (th22 (rail1 X6) (rail1 Y4) Gc_0))
(and5x4_1 (th22 (rail1 X5) (rail1 Y4) Gc_0))
(and5x4_0 (th12 (rail0 X5) (rail0 Y4) Gc_0))
(and4x5_1 (th22 (rail1 X4) (rail1 Y5) Gc_0))
(and4x5_0 (th12 (rail0 X4) (rail0 Y5) Gc_0))
(and5x7_0 (th12 (rail0 X5) (rail0 Y7) Gc_0))
(and5x7_1 (th22 (rail1 X5) (rail1 Y7) Gc_0))
(and5x1_0 (th12 (rail0 X5) (rail0 Y1) Gc_0))
(and5x1_1 (th22 (rail1 X5) (rail1 Y1) Gc_0))
(and3x3_0 (thand0 (rail0 Y3) (rail0 X3) (rail1 Y3) (rail1 X3) Gc_0))
(and3x3_1 (th22 (rail1 X3) (rail1 Y3) Gc_0))
(and3x1_0 (th12 (rail0 X3) (rail0 Y1) Gc_0))
(and3x1_1 (th22 (rail1 X3) (rail1 Y1) Gc_0))
(and1x1_0 (thand0 (rail0 Y1) (rail0 X1) (rail1 Y1) (rail1 X1) Gc_0))
(and1x1_1 (th22 (rail1 X1) (rail1 Y1) Gc_0))
(and3x7_0 (th12 (rail0 X3) (rail0 Y7) Gc_0))
(and3x7_1 (th22 (rail1 X3) (rail1 Y7) Gc_0))
(and1x3_0 (th12 (rail0 X1) (rail0 Y3) Gc_0))
(and1x3_1 (th22 (rail1 X1) (rail1 Y3) Gc_0))
(and7x0_1 (th22 (rail1 X7) (rail1 Y0) Gc_0))
(and7x0_0 (th12 (rail0 X7) (rail0 Y0) Gc_0))
(and2x2_0 (thand0 (rail0 Y2) (rail0 X2) (rail1 Y2) (rail1 X2) Gc_0))
(and2x2_1 (th22 (rail1 X2) (rail1 Y2) Gc_0))
(and7x7_0 (thand0 (rail0 Y7) (rail0 X7) (rail1 Y7) (rail1 X7) Gc_0))
(and7x7_1 (th22 (rail1 X7) (rail1 Y7) Gc_0))
(and7x5_0 (th12 (rail0 X7) (rail0 Y5) Gc_0))
(and7x5_1 (th22 (rail1 X7) (rail1 Y5) Gc_0))
(and0x1_1 (th22 (rail1 X0) (rail1 Y1) Gc_0))
(and0x1_0 (th12 (rail0 X0) (rail0 Y1) Gc_0))
(and5x3_0 (th12 (rail0 X5) (rail0 Y3) Gc_0))
(and5x3_1 (th22 (rail1 X5) (rail1 Y3) Gc_0))
(and7x3_0 (th12 (rail0 X7) (rail0 Y3) Gc_0))
(and7x3_1 (th22 (rail1 X7) (rail1 Y3) Gc_0))
(and0x3_1 (th22 (rail1 X0) (rail1 Y3) Gc_0))
(and0x3_0 (th12 (rail0 X0) (rail0 Y3) Gc_0))
(and5x5_0 (thand0 (rail0 Y5) (rail0 X5) (rail1 Y5) (rail1 X5) Gc_0))
(and5x5_1 (th22 (rail1 X5) (rail1 Y5) Gc_0))
(and3x2_1 (th22 (rail1 X3) (rail1 Y2) Gc_0))
(and3x2_0 (th12 (rail0 X3) (rail0 Y2) Gc_0))
(and3x5_0 (th12 (rail0 X3) (rail0 Y5) Gc_0))
(and3x5_1 (th22 (rail1 X3) (rail1 Y5) Gc_0))
(and3x0_1 (th22 (rail1 X3) (rail1 Y0) Gc_0))
(and3x0_0 (th12 (rail0 X3) (rail0 Y0) Gc_0))
(and3x6_1 (th22 (rail1 X3) (rail1 Y6) Gc_0))
(and3x6_0 (th12 (rail0 X3) (rail0 Y6) Gc_0))
)
(let
(
(C1x1_1 (th22 and0x1_1 and1x0_1 Gc_0))
(Z1_0 (th24comp and0x1_0 and1x0_1 and1x0_0 and0x1_1 Gc_0))
(Z1_1 (th24comp and0x1_0 and1x0_0 and0x1_1 and1x0_1 Gc_0))
(C1x1_0 (th12 and0x1_0 and1x0_0 Gc_0))
)
(let
(
(C1x2_1 (th23 and2x0_1 and1x1_1 C1x1_1 Gc_0))
(C1x2_0 (th23 and2x0_0 and1x1_0 C1x1_0 Gc_0))
)
(let
(
(S1x2_1 (th34w2 C1x2_0 and2x0_1 and1x1_1 C1x1_1 Gc_0))
(C1x3_0 (th23 and3x0_0 and2x1_0 C1x2_0 Gc_0))
(C1x3_1 (th23 and3x0_1 and2x1_1 C1x2_1 Gc_0))
(S1x2_0 (th34w2 C1x2_1 and2x0_0 and1x1_0 C1x1_0 Gc_0))
)
(let
(
(S1x3_0 (th34w2 C1x3_1 and3x0_0 and2x1_0 C1x2_0 Gc_0))
(S1x3_1 (th34w2 C1x3_0 and3x0_1 and2x1_1 C1x2_1 Gc_0))
(C1x4_1 (th23 and4x0_1 and3x1_1 C1x3_1 Gc_0))
(C1x4_0 (th23 and4x0_0 and3x1_0 C1x3_0 Gc_0))
(Z2_1 (th24comp S1x2_0 and0x2_0 S1x2_1 and0x2_1 Gc_0))
(Z2_0 (th24comp S1x2_0 and0x2_1 and0x2_0 S1x2_1 Gc_0))
(C2x2_0 (th12 S1x2_0 and0x2_0 Gc_0))
(C2x2_1 (th22 S1x2_1 and0x2_1 Gc_0))
)
(let
(
(C2x3_1 (th23 and1x2_1 S1x3_1 C2x2_1 Gc_0))
(C2x3_0 (th23 and1x2_0 S1x3_0 C2x2_0 Gc_0))
(C1x5_0 (th23 and5x0_0 and4x1_0 C1x4_0 Gc_0))
(C1x5_1 (th23 and5x0_1 and4x1_1 C1x4_1 Gc_0))
(S1x4_1 (th34w2 C1x4_0 and4x0_1 and3x1_1 C1x3_1 Gc_0))
(S1x4_0 (th34w2 C1x4_1 and4x0_0 and3x1_0 C1x3_0 Gc_0))
)
(let
(
(C2x4_0 (th23 and2x2_0 S1x4_0 C2x3_0 Gc_0))
(C2x4_1 (th23 and2x2_1 S1x4_1 C2x3_1 Gc_0))
(C1x6_1 (th23 and6x0_1 and5x1_1 C1x5_1 Gc_0))
(C1x6_0 (th23 and6x0_0 and5x1_0 C1x5_0 Gc_0))
(S2x3_1 (th34w2 C2x3_0 and1x2_1 S1x3_1 C2x2_1 Gc_0))
(S2x3_0 (th34w2 C2x3_1 and1x2_0 S1x3_0 C2x2_0 Gc_0))
(S1x5_0 (th34w2 C1x5_1 and5x0_0 and4x1_0 C1x4_0 Gc_0))
(S1x5_1 (th34w2 C1x5_0 and5x0_1 and4x1_1 C1x4_1 Gc_0))
)
(let
(
(S1x6_1 (th34w2 C1x6_0 and6x0_1 and5x1_1 C1x5_1 Gc_0))
(S1x6_0 (th34w2 C1x6_1 and6x0_0 and5x1_0 C1x5_0 Gc_0))
(C1x7_0 (th23 and7x0_0 and6x1_0 C1x6_0 Gc_0))
(C2x5_1 (th23 and3x2_1 S1x5_1 C2x4_1 Gc_0))
(C2x5_0 (th23 and3x2_0 S1x5_0 C2x4_0 Gc_0))
(Z3_0 (th24comp S2x3_0 and0x3_1 and0x3_0 S2x3_1 Gc_0))
(Z3_1 (th24comp S2x3_0 and0x3_0 S2x3_1 and0x3_1 Gc_0))
(S2x4_0 (th34w2 C2x4_1 and2x2_0 S1x4_0 C2x3_0 Gc_0))
(S2x4_1 (th34w2 C2x4_0 and2x2_1 S1x4_1 C2x3_1 Gc_0))
(C3x3_0 (th12 S2x3_0 and0x3_0 Gc_0))
(C3x3_1 (th22 S2x3_1 and0x3_1 Gc_0))
(C1x7_1 (th23 and7x0_1 and6x1_1 C1x6_1 Gc_0))
)
(let
(
(C3x4_1 (th23 and1x3_1 S2x4_1 C3x3_1 Gc_0))
(C3x4_0 (th23 and1x3_0 S2x4_0 C3x3_0 Gc_0))
(S1x7_0 (th34w2 C1x7_1 and7x0_0 and6x1_0 C1x6_0 Gc_0))
(S1x7_1 (th34w2 C1x7_0 and7x0_1 and6x1_1 C1x6_1 Gc_0))
(S2x5_1 (th34w2 C2x5_0 and3x2_1 S1x5_1 C2x4_1 Gc_0))
(S2x5_0 (th34w2 C2x5_1 and3x2_0 S1x5_0 C2x4_0 Gc_0))
(C2x6_0 (th23 and4x2_0 S1x6_0 C2x5_0 Gc_0))
(C2x6_1 (th23 and4x2_1 S1x6_1 C2x5_1 Gc_0))
)
(let
(
(C2x7_1 (th23 and5x2_1 S1x7_1 C2x6_1 Gc_0))
(C2x7_0 (th23 and5x2_0 S1x7_0 C2x6_0 Gc_0))
(S2x6_0 (th34w2 C2x6_1 and4x2_0 S1x6_0 C2x5_0 Gc_0))
(S2x6_1 (th34w2 C2x6_0 and4x2_1 S1x6_1 C2x5_1 Gc_0))
(S3x4_1 (th34w2 C3x4_0 and1x3_1 S2x4_1 C3x3_1 Gc_0))
(S3x4_0 (th34w2 C3x4_1 and1x3_0 S2x4_0 C3x3_0 Gc_0))
(C3x5_0 (th23 and2x3_0 S2x5_0 C3x4_0 Gc_0))
(C3x5_1 (th23 and2x3_1 S2x5_1 C3x4_1 Gc_0))
)
(let
(
(Z4_1 (th24comp S3x4_0 and0x4_0 S3x4_1 and0x4_1 Gc_0))
(Z4_0 (th24comp S3x4_0 and0x4_1 and0x4_0 S3x4_1 Gc_0))
(S3x5_0 (th34w2 C3x5_1 and2x3_0 S2x5_0 C3x4_0 Gc_0))
(S3x5_1 (th34w2 C3x5_0 and2x3_1 S2x5_1 C3x4_1 Gc_0))
(C4x4_0 (th12 S3x4_0 and0x4_0 Gc_0))
(C4x4_1 (th22 S3x4_1 and0x4_1 Gc_0))
(C2x8_0 (th23 and7x1_0 C1x7_0 C2x7_0 Gc_0))
(C2x8_1 (th23 and7x1_1 C1x7_1 C2x7_1 Gc_0))
(S2x7_1 (th34w2 C2x7_0 and5x2_1 S1x7_1 C2x6_1 Gc_0))
(S2x7_0 (th34w2 C2x7_1 and5x2_0 S1x7_0 C2x6_0 Gc_0))
(C3x6_1 (th23 and3x3_1 S2x6_1 C3x5_1 Gc_0))
(C3x6_0 (th23 and3x3_0 S2x6_0 C3x5_0 Gc_0))
)
(let
(
(S2x8_0 (th34w2 C2x8_1 and7x1_0 C1x7_0 C2x7_0 Gc_0))
(S2x8_1 (th34w2 C2x8_0 and7x1_1 C1x7_1 C2x7_1 Gc_0))
(S3x6_1 (th34w2 C3x6_0 and3x3_1 S2x6_1 C3x5_1 Gc_0))
(S3x6_0 (th34w2 C3x6_1 and3x3_0 S2x6_0 C3x5_0 Gc_0))
(C4x5_1 (th23 and1x4_1 S3x5_1 C4x4_1 Gc_0))
(C4x5_0 (th23 and1x4_0 S3x5_0 C4x4_0 Gc_0))
(C3x7_0 (th23 and4x3_0 S2x7_0 C3x6_0 Gc_0))
(C3x7_1 (th23 and4x3_1 S2x7_1 C3x6_1 Gc_0))
)
(let
(
(S4x5_1 (th34w2 C4x5_0 and1x4_1 S3x5_1 C4x4_1 Gc_0))
(S4x5_0 (th34w2 C4x5_1 and1x4_0 S3x5_0 C4x4_0 Gc_0))
(C3x8_1 (th23 and6x2_1 S2x8_1 C3x7_1 Gc_0))
(C3x8_0 (th23 and6x2_0 S2x8_0 C3x7_0 Gc_0))
(S3x7_0 (th34w2 C3x7_1 and4x3_0 S2x7_0 C3x6_0 Gc_0))
(S3x7_1 (th34w2 C3x7_0 and4x3_1 S2x7_1 C3x6_1 Gc_0))
(C4x6_0 (th23 and2x4_0 S3x6_0 C4x5_0 Gc_0))
(C4x6_1 (th23 and2x4_1 S3x6_1 C4x5_1 Gc_0))
)
(let
(
(C4x7_1 (th23 and3x4_1 S3x7_1 C4x6_1 Gc_0))
(C4x7_0 (th23 and3x4_0 S3x7_0 C4x6_0 Gc_0))
(S4x6_0 (th34w2 C4x6_1 and2x4_0 S3x6_0 C4x5_0 Gc_0))
(S4x6_1 (th34w2 C4x6_0 and2x4_1 S3x6_1 C4x5_1 Gc_0))
(C5x5_0 (th12 S4x5_0 and0x5_0 Gc_0))
(C5x5_1 (th22 S4x5_1 and0x5_1 Gc_0))
(S3x8_1 (th34w2 C3x8_0 and6x2_1 S2x8_1 C3x7_1 Gc_0))
(S3x8_0 (th34w2 C3x8_1 and6x2_0 S2x8_0 C3x7_0 Gc_0))
(C3x9_0 (th23 and7x2_0 C2x8_0 C3x8_0 Gc_0))
(C3x9_1 (th23 and7x2_1 C2x8_1 C3x8_1 Gc_0))
(Z5_0 (th24comp S4x5_0 and0x5_1 and0x5_0 S4x5_1 Gc_0))
(Z5_1 (th24comp S4x5_0 and0x5_0 S4x5_1 and0x5_1 Gc_0))
)
(let
(
(C5x6_1 (th23 and1x5_1 S4x6_1 C5x5_1 Gc_0))
(S3x9_0 (th34w2 C3x9_1 and7x2_0 C2x8_0 C3x8_0 Gc_0))
(S3x9_1 (th34w2 C3x9_0 and7x2_1 C2x8_1 C3x8_1 Gc_0))
(C5x6_0 (th23 and1x5_0 S4x6_0 C5x5_0 Gc_0))
(S4x7_1 (th34w2 C4x7_0 and3x4_1 S3x7_1 C4x6_1 Gc_0))
(S4x7_0 (th34w2 C4x7_1 and3x4_0 S3x7_0 C4x6_0 Gc_0))
(C4x8_0 (th23 and5x3_0 S3x8_0 C4x7_0 Gc_0))
(C4x8_1 (th23 and5x3_1 S3x8_1 C4x7_1 Gc_0))
)
(let
(
(C5x7_0 (th23 and2x5_0 S4x7_0 C5x6_0 Gc_0))
(C5x7_1 (th23 and2x5_1 S4x7_1 C5x6_1 Gc_0))
(S4x8_0 (th34w2 C4x8_1 and5x3_0 S3x8_0 C4x7_0 Gc_0))
(S4x8_1 (th34w2 C4x8_0 and5x3_1 S3x8_1 C4x7_1 Gc_0))
(S5x6_1 (th34w2 C5x6_0 and1x5_1 S4x6_1 C5x5_1 Gc_0))
(S5x6_0 (th34w2 C5x6_1 and1x5_0 S4x6_0 C5x5_0 Gc_0))
(C4x9_1 (th23 and6x3_1 S3x9_1 C4x8_1 Gc_0))
(C4x9_0 (th23 and6x3_0 S3x9_0 C4x8_0 Gc_0))
)
(let
(
(C4x10_0 (th23 and7x3_0 C3x9_0 C4x9_0 Gc_0))
(C6x6_0 (th12 S5x6_0 and0x6_0 Gc_0))
(C6x6_1 (th22 S5x6_1 and0x6_1 Gc_0))
(S4x9_1 (th34w2 C4x9_0 and6x3_1 S3x9_1 C4x8_1 Gc_0))
(S4x9_0 (th34w2 C4x9_1 and6x3_0 S3x9_0 C4x8_0 Gc_0))
(Z6_1 (th24comp S5x6_0 and0x6_0 S5x6_1 and0x6_1 Gc_0))
(Z6_0 (th24comp S5x6_0 and0x6_1 and0x6_0 S5x6_1 Gc_0))
(S5x7_0 (th34w2 C5x7_1 and2x5_0 S4x7_0 C5x6_0 Gc_0))
(S5x7_1 (th34w2 C5x7_0 and2x5_1 S4x7_1 C5x6_1 Gc_0))
(C5x8_1 (th23 and4x4_1 S4x8_1 C5x7_1 Gc_0))
(C5x8_0 (th23 and4x4_0 S4x8_0 C5x7_0 Gc_0))
(C4x10_1 (th23 and7x3_1 C3x9_1 C4x9_1 Gc_0))
)
(let
(
(S5x8_1 (th34w2 C5x8_0 and4x4_1 S4x8_1 C5x7_1 Gc_0))
(S5x8_0 (th34w2 C5x8_1 and4x4_0 S4x8_0 C5x7_0 Gc_0))
(C5x9_0 (th23 and5x4_0 S4x9_0 C5x8_0 Gc_0))
(C5x9_1 (th23 and5x4_1 S4x9_1 C5x8_1 Gc_0))
(C6x7_1 (th23 and1x6_1 S5x7_1 C6x6_1 Gc_0))
(C6x7_0 (th23 and1x6_0 S5x7_0 C6x6_0 Gc_0))
(S4x10_0 (th34w2 C4x10_1 and7x3_0 C3x9_0 C4x9_0 Gc_0))
(S4x10_1 (th34w2 C4x10_0 and7x3_1 C3x9_1 C4x9_1 Gc_0))
)
(let
(
(C5x10_1 (th23 and6x4_1 S4x10_1 C5x9_1 Gc_0))
(C5x10_0 (th23 and6x4_0 S4x10_0 C5x9_0 Gc_0))
(S6x7_1 (th34w2 C6x7_0 and1x6_1 S5x7_1 C6x6_1 Gc_0))
(S6x7_0 (th34w2 C6x7_1 and1x6_0 S5x7_0 C6x6_0 Gc_0))
(C6x8_0 (th23 and3x5_0 S5x8_0 C6x7_0 Gc_0))
(C6x8_1 (th23 and3x5_1 S5x8_1 C6x7_1 Gc_0))
(S5x9_0 (th34w2 C5x9_1 and5x4_0 S4x9_0 C5x8_0 Gc_0))
(S5x9_1 (th34w2 C5x9_0 and5x4_1 S4x9_1 C5x8_1 Gc_0))
)
(let
(
(C6x9_1 (th23 and4x5_1 S5x9_1 C6x8_1 Gc_0))
(C6x9_0 (th23 and4x5_0 S5x9_0 C6x8_0 Gc_0))
(S5x10_0 (th34w2 C5x10_1 and6x4_0 S4x10_0 C5x9_0 Gc_0))
(S6x8_0 (th34w2 C6x8_1 and3x5_0 S5x8_0 C6x7_0 Gc_0))
(S6x8_1 (th34w2 C6x8_0 and3x5_1 S5x8_1 C6x7_1 Gc_0))
(C5x11_0 (th23 and7x4_0 C4x10_0 C5x10_0 Gc_0))
(S5x10_1 (th34w2 C5x10_0 and6x4_1 S4x10_1 C5x9_1 Gc_0))
(Z7_0 (th24comp S6x7_0 and0x7_1 and0x7_0 S6x7_1 Gc_0))
(C7x7_0 (th12 S6x7_0 and0x7_0 Gc_0))
(C7x7_1 (th22 S6x7_1 and0x7_1 Gc_0))
(C5x11_1 (th23 and7x4_1 C4x10_1 C5x10_1 Gc_0))
(Z7_1 (th24comp S6x7_0 and0x7_0 S6x7_1 and0x7_1 Gc_0))
)
(let
(
(S6x9_0 (th34w2 C6x9_1 and4x5_0 S5x9_0 C6x8_0 Gc_0))
(S6x9_1 (th34w2 C6x9_0 and4x5_1 S5x9_1 C6x8_1 Gc_0))
(C7x8_1 (th23 and2x6_1 S6x8_1 C7x7_1 Gc_0))
(C6x10_0 (th23 and5x5_0 S5x10_0 C6x9_0 Gc_0))
(C6x10_1 (th23 and5x5_1 S5x10_1 C6x9_1 Gc_0))
(C7x8_0 (th23 and2x6_0 S6x8_0 C7x7_0 Gc_0))
(S5x11_0 (th34w2 C5x11_1 and7x4_0 C4x10_0 C5x10_0 Gc_0))
(S5x11_1 (th34w2 C5x11_0 and7x4_1 C4x10_1 C5x10_1 Gc_0))
)
(let
(
(S6x10_0 (th34w2 C6x10_1 and5x5_0 S5x10_0 C6x9_0 Gc_0))
(S6x10_1 (th34w2 C6x10_0 and5x5_1 S5x10_1 C6x9_1 Gc_0))
(S7x8_1 (th34w2 C7x8_0 and2x6_1 S6x8_1 C7x7_1 Gc_0))
(S7x8_0 (th34w2 C7x8_1 and2x6_0 S6x8_0 C7x7_0 Gc_0))
(C6x11_1 (th23 and6x5_1 S5x11_1 C6x10_1 Gc_0))
(C6x11_0 (th23 and6x5_0 S5x11_0 C6x10_0 Gc_0))
(C7x9_0 (th23 and3x6_0 S6x9_0 C7x8_0 Gc_0))
(C7x9_1 (th23 and3x6_1 S6x9_1 C7x8_1 Gc_0))
)
(let
(
(S7x9_0 (th34w2 C7x9_1 and3x6_0 S6x9_0 C7x8_0 Gc_0))
(S7x9_1 (th34w2 C7x9_0 and3x6_1 S6x9_1 C7x8_1 Gc_0))
(C6x12_0 (th23 and7x5_0 C5x11_0 C6x11_0 Gc_0))
(Z8_0 (th24comp S7x8_0 and1x7_1 and1x7_0 S7x8_1 Gc_0))
(C8x8_0 (th12 S7x8_0 and1x7_0 Gc_0))
(C8x8_1 (th22 S7x8_1 and1x7_1 Gc_0))
(Z8_1 (th24comp S7x8_0 and1x7_0 S7x8_1 and1x7_1 Gc_0))
(C6x12_1 (th23 and7x5_1 C5x11_1 C6x11_1 Gc_0))
(C7x10_1 (th23 and4x6_1 S6x10_1 C7x9_1 Gc_0))
(C7x10_0 (th23 and4x6_0 S6x10_0 C7x9_0 Gc_0))
(S6x11_1 (th34w2 C6x11_0 and6x5_1 S5x11_1 C6x10_1 Gc_0))
(S6x11_0 (th34w2 C6x11_1 and6x5_0 S5x11_0 C6x10_0 Gc_0))
)
(let
(
(S7x10_1 (th34w2 C7x10_0 and4x6_1 S6x10_1 C7x9_1 Gc_0))
(S7x10_0 (th34w2 C7x10_1 and4x6_0 S6x10_0 C7x9_0 Gc_0))
(C8x9_1 (th23 and2x7_1 S7x9_1 C8x8_1 Gc_0))
(S6x12_0 (th34w2 C6x12_1 and7x5_0 C5x11_0 C6x11_0 Gc_0))
(S6x12_1 (th34w2 C6x12_0 and7x5_1 C5x11_1 C6x11_1 Gc_0))
(C8x9_0 (th23 and2x7_0 S7x9_0 C8x8_0 Gc_0))
(C7x11_0 (th23 and5x6_0 S6x11_0 C7x10_0 Gc_0))
(C7x11_1 (th23 and5x6_1 S6x11_1 C7x10_1 Gc_0))
)
(let
(
(C8x10_0 (th23 and3x7_0 S7x10_0 C8x9_0 Gc_0))
(C8x10_1 (th23 and3x7_1 S7x10_1 C8x9_1 Gc_0))
(S7x11_0 (th34w2 C7x11_1 and5x6_0 S6x11_0 C7x10_0 Gc_0))
(S7x11_1 (th34w2 C7x11_0 and5x6_1 S6x11_1 C7x10_1 Gc_0))
(C7x12_1 (th23 and6x6_1 S6x12_1 C7x11_1 Gc_0))
(C7x12_0 (th23 and6x6_0 S6x12_0 C7x11_0 Gc_0))
(Z9_0 (th34w2 C8x9_1 and2x7_0 S7x9_0 C8x8_0 Gc_0))
(Z9_1 (th34w2 C8x9_0 and2x7_1 S7x9_1 C8x8_1 Gc_0))
)
(let
(
(C7x13_0 (th23 and7x6_0 C6x12_0 C7x12_0 Gc_0))
(C7x13_1 (th23 and7x6_1 C6x12_1 C7x12_1 Gc_0))
(C8x11_1 (th23 and4x7_1 S7x11_1 C8x10_1 Gc_0))
(C8x11_0 (th23 and4x7_0 S7x11_0 C8x10_0 Gc_0))
(S7x12_1 (th34w2 C7x12_0 and6x6_1 S6x12_1 C7x11_1 Gc_0))
(S7x12_0 (th34w2 C7x12_1 and6x6_0 S6x12_0 C7x11_0 Gc_0))
(Z10_1 (th34w2 C8x10_0 and3x7_1 S7x10_1 C8x9_1 Gc_0))
(Z10_0 (th34w2 C8x10_1 and3x7_0 S7x10_0 C8x9_0 Gc_0))
)
(let
(
(Z11_0 (th34w2 C8x11_1 and4x7_0 S7x11_0 C8x10_0 Gc_0))
(Z11_1 (th34w2 C8x11_0 and4x7_1 S7x11_1 C8x10_1 Gc_0))
(S7x13_0 (th34w2 C7x13_1 and7x6_0 C6x12_0 C7x12_0 Gc_0))
(S7x13_1 (th34w2 C7x13_0 and7x6_1 C6x12_1 C7x12_1 Gc_0))
(C8x12_0 (th23 and5x7_0 S7x12_0 C8x11_0 Gc_0))
(C8x12_1 (th23 and5x7_1 S7x12_1 C8x11_1 Gc_0))
)
(let
(
(Z12_1 (th34w2 C8x12_0 and5x7_1 S7x12_1 C8x11_1 Gc_0))
(Z12_0 (th34w2 C8x12_1 and5x7_0 S7x12_0 C8x11_0 Gc_0))
(C8x13_1 (th23 and6x7_1 S7x13_1 C8x12_1 Gc_0))
(C8x13_0 (th23 and6x7_0 S7x13_0 C8x12_0 Gc_0))
)
(let
(
(Z15_0 (th23 and7x7_0 C7x13_0 C8x13_0 Gc_0))
(Z15_1 (th23 and7x7_1 C7x13_1 C8x13_1 Gc_0))
(Z13_0 (th34w2 C8x13_1 and6x7_0 S7x13_0 C8x12_0 Gc_0))
(Z13_1 (th34w2 C8x13_0 and6x7_1 S7x13_1 C8x12_1 Gc_0))
)
(let
(
(Z14_1 (th34w2 Z15_0 and7x7_1 C7x13_1 C8x13_1 Gc_0))
(Z14_0 (th34w2 Z15_1 and7x7_0 C7x13_0 C8x13_0 Gc_0))
)
(let
(
(Z0 (concat Z0_1 Z0_0))
(Z1 (concat Z1_1 Z1_0))
(Z2 (concat Z2_1 Z2_0))
(Z3 (concat Z3_1 Z3_0))
(Z4 (concat Z4_1 Z4_0))
(Z5 (concat Z5_1 Z5_0))
(Z6 (concat Z6_1 Z6_0))
(Z7 (concat Z7_1 Z7_0))
(Z8 (concat Z8_1 Z8_0))
(Z9 (concat Z9_1 Z9_0))
(Z10 (concat Z10_1 Z10_0))
(Z11 (concat Z11_1 Z11_0))
(Z12 (concat Z12_1 Z12_0))
(Z13 (concat Z13_1 Z13_0))
(Z14 (concat Z14_1 Z14_0))
(Z15 (concat Z15_1 Z15_0))
)
(let
(
(and1x6_sync (bvand (rail1 X1) (rail1 Y6))) 
(and1x7_sync (bvand (rail1 X1) (rail1 Y7))) 
(and1x4_sync (bvand (rail1 X1) (rail1 Y4))) 
(and1x5_sync (bvand (rail1 X1) (rail1 Y5))) 
(and1x2_sync (bvand (rail1 X1) (rail1 Y2))) 
(and1x3_sync (bvand (rail1 X1) (rail1 Y3))) 
(and1x0_sync (bvand (rail1 X1) (rail1 Y0))) 
(and1x1_sync (bvand (rail1 X1) (rail1 Y1))) 
(and0x7_sync (bvand (rail1 X0) (rail1 Y7))) 
(and0x6_sync (bvand (rail1 X0) (rail1 Y6))) 
(and0x5_sync (bvand (rail1 X0) (rail1 Y5))) 
(and0x4_sync (bvand (rail1 X0) (rail1 Y4))) 
(and0x3_sync (bvand (rail1 X0) (rail1 Y3))) 
(and0x2_sync (bvand (rail1 X0) (rail1 Y2))) 
(and0x1_sync (bvand (rail1 X0) (rail1 Y1))) 
(and5x2_sync (bvand (rail1 X5) (rail1 Y2))) 
(and5x3_sync (bvand (rail1 X5) (rail1 Y3))) 
(and5x0_sync (bvand (rail1 X5) (rail1 Y0))) 
(and5x1_sync (bvand (rail1 X5) (rail1 Y1))) 
(and5x6_sync (bvand (rail1 X5) (rail1 Y6))) 
(and5x7_sync (bvand (rail1 X5) (rail1 Y7))) 
(and5x4_sync (bvand (rail1 X5) (rail1 Y4))) 
(and5x5_sync (bvand (rail1 X5) (rail1 Y5))) 
(and4x3_sync (bvand (rail1 X4) (rail1 Y3))) 
(and4x2_sync (bvand (rail1 X4) (rail1 Y2))) 
(and4x1_sync (bvand (rail1 X4) (rail1 Y1))) 
(and4x0_sync (bvand (rail1 X4) (rail1 Y0))) 
(and4x7_sync (bvand (rail1 X4) (rail1 Y7))) 
(and4x6_sync (bvand (rail1 X4) (rail1 Y6))) 
(and4x5_sync (bvand (rail1 X4) (rail1 Y5))) 
(and4x4_sync (bvand (rail1 X4) (rail1 Y4))) 
(and2x5_sync (bvand (rail1 X2) (rail1 Y5))) 
(and2x4_sync (bvand (rail1 X2) (rail1 Y4))) 
(and2x7_sync (bvand (rail1 X2) (rail1 Y7))) 
(and2x6_sync (bvand (rail1 X2) (rail1 Y6))) 
(and2x1_sync (bvand (rail1 X2) (rail1 Y1))) 
(and2x0_sync (bvand (rail1 X2) (rail1 Y0))) 
(and2x3_sync (bvand (rail1 X2) (rail1 Y3))) 
(and2x2_sync (bvand (rail1 X2) (rail1 Y2))) 
(and7x0_sync (bvand (rail1 X7) (rail1 Y0))) 
(and7x1_sync (bvand (rail1 X7) (rail1 Y1))) 
(and7x2_sync (bvand (rail1 X7) (rail1 Y2))) 
(and7x3_sync (bvand (rail1 X7) (rail1 Y3))) 
(and7x4_sync (bvand (rail1 X7) (rail1 Y4))) 
(and7x5_sync (bvand (rail1 X7) (rail1 Y5))) 
(and7x6_sync (bvand (rail1 X7) (rail1 Y6))) 
(and7x7_sync (bvand (rail1 X7) (rail1 Y7))) 
(and6x1_sync (bvand (rail1 X6) (rail1 Y1))) 
(and6x0_sync (bvand (rail1 X6) (rail1 Y0))) 
(and6x3_sync (bvand (rail1 X6) (rail1 Y3))) 
(and6x2_sync (bvand (rail1 X6) (rail1 Y2))) 
(and6x5_sync (bvand (rail1 X6) (rail1 Y5))) 
(and6x4_sync (bvand (rail1 X6) (rail1 Y4))) 
(and6x7_sync (bvand (rail1 X6) (rail1 Y7))) 
(and6x6_sync (bvand (rail1 X6) (rail1 Y6))) 
(Z0_sync (bvand (rail1 X0) (rail1 Y0))) 
(and3x4_sync (bvand (rail1 X3) (rail1 Y4))) 
(and3x5_sync (bvand (rail1 X3) (rail1 Y5))) 
(and3x6_sync (bvand (rail1 X3) (rail1 Y6))) 
(and3x7_sync (bvand (rail1 X3) (rail1 Y7))) 
(and3x0_sync (bvand (rail1 X3) (rail1 Y0))) 
(and3x1_sync (bvand (rail1 X3) (rail1 Y1))) 
(and3x2_sync (bvand (rail1 X3) (rail1 Y2))) 
(and3x3_sync (bvand (rail1 X3) (rail1 Y3))) 
)
(let
(
(I9_sync (bvxor and5x0_sync and4x1_sync)) 
(I8_sync (bvand and4x0_sync and3x1_sync)) 
(I12_sync (bvxor and6x0_sync and5x1_sync)) 
(C1x1_sync (bvand and1x0_sync and0x1_sync)) 
(I15_sync (bvxor and7x0_sync and6x1_sync)) 
(I14_sync (bvand and6x0_sync and5x1_sync)) 
(I17_sync (bvand and7x0_sync and6x1_sync)) 
(I2_sync (bvand and2x0_sync and1x1_sync)) 
(I11_sync (bvand and5x0_sync and4x1_sync)) 
(I6_sync (bvxor and4x0_sync and3x1_sync)) 
(I0_sync (bvxor and2x0_sync and1x1_sync)) 
(I5_sync (bvand and3x0_sync and2x1_sync)) 
(Z1_sync (bvxor and1x0_sync and0x1_sync)) 
(I3_sync (bvxor and3x0_sync and2x1_sync)) 
)
(let
(
(I1_sync (bvand I0_sync C1x1_sync)) 
(S1x2_sync (bvxor I0_sync C1x1_sync)) 
)
(let
(
(C2x2_sync (bvand and0x2_sync S1x2_sync)) 
(C1x2_sync (bvor I1_sync I2_sync)) 
(Z2_sync (bvxor and0x2_sync S1x2_sync)) 
)
(let
(
(I4_sync (bvand I3_sync C1x2_sync)) 
(S1x3_sync (bvxor I3_sync C1x2_sync)) 
)
(let
(
(I20_sync (bvand and1x2_sync S1x3_sync)) 
(I18_sync (bvxor and1x2_sync S1x3_sync)) 
(C1x3_sync (bvor I4_sync I5_sync)) 
)
(let
(
(S1x4_sync (bvxor I6_sync C1x3_sync)) 
(I19_sync (bvand I18_sync C2x2_sync)) 
(S2x3_sync (bvxor I18_sync C2x2_sync)) 
(I7_sync (bvand I6_sync C1x3_sync)) 
)
(let
(
(C1x4_sync (bvor I7_sync I8_sync)) 
(I21_sync (bvxor and2x2_sync S1x4_sync)) 
(I23_sync (bvand and2x2_sync S1x4_sync)) 
(C2x3_sync (bvor I19_sync I20_sync)) 
(C3x3_sync (bvand and0x3_sync S2x3_sync)) 
(Z3_sync (bvxor and0x3_sync S2x3_sync)) 
)
(let
(
(S1x5_sync (bvxor I9_sync C1x4_sync)) 
(I22_sync (bvand I21_sync C2x3_sync)) 
(S2x4_sync (bvxor I21_sync C2x3_sync)) 
(I10_sync (bvand I9_sync C1x4_sync)) 
)
(let
(
(C1x5_sync (bvor I10_sync I11_sync)) 
(I38_sync (bvand and1x3_sync S2x4_sync)) 
(C2x4_sync (bvor I22_sync I23_sync)) 
(I24_sync (bvxor and3x2_sync S1x5_sync)) 
(I36_sync (bvxor and1x3_sync S2x4_sync)) 
(I26_sync (bvand and3x2_sync S1x5_sync)) 
)
(let
(
(S3x4_sync (bvxor I36_sync C3x3_sync)) 
(I37_sync (bvand I36_sync C3x3_sync)) 
(I25_sync (bvand I24_sync C2x4_sync)) 
(I13_sync (bvand I12_sync C1x5_sync)) 
(S1x6_sync (bvxor I12_sync C1x5_sync)) 
(S2x5_sync (bvxor I24_sync C2x4_sync)) 
)
(let
(
(I29_sync (bvand and4x2_sync S1x6_sync)) 
(I39_sync (bvxor and2x3_sync S2x5_sync)) 
(C2x5_sync (bvor I25_sync I26_sync)) 
(C1x6_sync (bvor I13_sync I14_sync)) 
(I27_sync (bvxor and4x2_sync S1x6_sync)) 
(C3x4_sync (bvor I37_sync I38_sync)) 
(Z4_sync (bvxor and0x4_sync S3x4_sync)) 
(C4x4_sync (bvand and0x4_sync S3x4_sync)) 
(I41_sync (bvand and2x3_sync S2x5_sync)) 
)
(let
(
(I28_sync (bvand I27_sync C2x5_sync)) 
(S3x5_sync (bvxor I39_sync C3x4_sync)) 
(I16_sync (bvand I15_sync C1x6_sync)) 
(S1x7_sync (bvxor I15_sync C1x6_sync)) 
(S2x6_sync (bvxor I27_sync C2x5_sync)) 
(I40_sync (bvand I39_sync C3x4_sync)) 
)
(let
(
(C1x7_sync (bvor I16_sync I17_sync)) 
(C2x6_sync (bvor I28_sync I29_sync)) 
(I30_sync (bvxor and5x2_sync S1x7_sync)) 
(C3x5_sync (bvor I40_sync I41_sync)) 
(I32_sync (bvand and5x2_sync S1x7_sync)) 
(I44_sync (bvand and3x3_sync S2x6_sync)) 
(I42_sync (bvxor and3x3_sync S2x6_sync)) 
(I54_sync (bvxor and1x4_sync S3x5_sync)) 
(I56_sync (bvand and1x4_sync S3x5_sync)) 
)
(let
(
(S3x6_sync (bvxor I42_sync C3x5_sync)) 
(I33_sync (bvxor and7x1_sync C1x7_sync)) 
(I31_sync (bvand I30_sync C2x6_sync)) 
(S4x5_sync (bvxor I54_sync C4x4_sync)) 
(I35_sync (bvand and7x1_sync C1x7_sync)) 
(S2x7_sync (bvxor I30_sync C2x6_sync)) 
(I55_sync (bvand I54_sync C4x4_sync)) 
(I43_sync (bvand I42_sync C3x5_sync)) 
)
(let
(
(C3x6_sync (bvor I43_sync I44_sync)) 
(C2x7_sync (bvor I31_sync I32_sync)) 
(I59_sync (bvand and2x4_sync S3x6_sync)) 
(C5x5_sync (bvand and0x5_sync S4x5_sync)) 
(I47_sync (bvand and4x3_sync S2x7_sync)) 
(Z5_sync (bvxor and0x5_sync S4x5_sync)) 
(I45_sync (bvxor and4x3_sync S2x7_sync)) 
(C4x5_sync (bvor I55_sync I56_sync)) 
(I57_sync (bvxor and2x4_sync S3x6_sync)) 
)
(let
(
(S3x7_sync (bvxor I45_sync C3x6_sync)) 
(S4x6_sync (bvxor I57_sync C4x5_sync)) 
(I58_sync (bvand I57_sync C4x5_sync)) 
(S2x8_sync (bvxor I33_sync C2x7_sync)) 
(I46_sync (bvand I45_sync C3x6_sync)) 
(I34_sync (bvand I33_sync C2x7_sync)) 
)
(let
(
(I48_sync (bvxor and6x2_sync S2x8_sync)) 
(C2x8_sync (bvor I34_sync I35_sync)) 
(C3x7_sync (bvor I46_sync I47_sync)) 
(I74_sync (bvand and1x5_sync S4x6_sync)) 
(I60_sync (bvxor and3x4_sync S3x7_sync)) 
(I72_sync (bvxor and1x5_sync S4x6_sync)) 
(I62_sync (bvand and3x4_sync S3x7_sync)) 
(I50_sync (bvand and6x2_sync S2x8_sync)) 
(C4x6_sync (bvor I58_sync I59_sync)) 
)
(let
(
(S3x8_sync (bvxor I48_sync C3x7_sync)) 
(S5x6_sync (bvxor I72_sync C5x5_sync)) 
(S4x7_sync (bvxor I60_sync C4x6_sync)) 
(I73_sync (bvand I72_sync C5x5_sync)) 
(I61_sync (bvand I60_sync C4x6_sync)) 
(I49_sync (bvand I48_sync C3x7_sync)) 
(I51_sync (bvxor and7x2_sync C2x8_sync)) 
(I53_sync (bvand and7x2_sync C2x8_sync)) 
)
(let
(
(I77_sync (bvand and2x5_sync S4x7_sync)) 
(I65_sync (bvand and5x3_sync S3x8_sync)) 
(I75_sync (bvxor and2x5_sync S4x7_sync)) 
(C4x7_sync (bvor I61_sync I62_sync)) 
(C5x6_sync (bvor I73_sync I74_sync)) 
(I63_sync (bvxor and5x3_sync S3x8_sync)) 
(Z6_sync (bvxor and0x6_sync S5x6_sync)) 
(C6x6_sync (bvand and0x6_sync S5x6_sync)) 
(C3x8_sync (bvor I49_sync I50_sync)) 
)
(let
(
(S4x8_sync (bvxor I63_sync C4x7_sync)) 
(S5x7_sync (bvxor I75_sync C5x6_sync)) 
(S3x9_sync (bvxor I51_sync C3x8_sync)) 
(I64_sync (bvand I63_sync C4x7_sync)) 
(I76_sync (bvand I75_sync C5x6_sync)) 
(I52_sync (bvand I51_sync C3x8_sync)) 
)
(let
(
(C5x7_sync (bvor I76_sync I77_sync)) 
(C4x8_sync (bvor I64_sync I65_sync)) 
(I66_sync (bvxor and6x3_sync S3x9_sync)) 
(I90_sync (bvxor and1x6_sync S5x7_sync)) 
(I92_sync (bvand and1x6_sync S5x7_sync)) 
(I80_sync (bvand and4x4_sync S4x8_sync)) 
(C3x9_sync (bvor I52_sync I53_sync)) 
(I68_sync (bvand and6x3_sync S3x9_sync)) 
(I78_sync (bvxor and4x4_sync S4x8_sync)) 
)
(let
(
(S4x9_sync (bvxor I66_sync C4x8_sync)) 
(S5x8_sync (bvxor I78_sync C5x7_sync)) 
(S6x7_sync (bvxor I90_sync C6x6_sync)) 
(I67_sync (bvand I66_sync C4x8_sync)) 
(I91_sync (bvand I90_sync C6x6_sync)) 
(I71_sync (bvand and7x3_sync C3x9_sync)) 
(I69_sync (bvxor and7x3_sync C3x9_sync)) 
(I79_sync (bvand I78_sync C5x7_sync)) 
)
(let
(
(I95_sync (bvand and3x5_sync S5x8_sync)) 
(I81_sync (bvxor and5x4_sync S4x9_sync)) 
(C4x9_sync (bvor I67_sync I68_sync)) 
(C7x7_sync (bvand and0x7_sync S6x7_sync)) 
(I93_sync (bvxor and3x5_sync S5x8_sync)) 
(C5x8_sync (bvor I79_sync I80_sync)) 
(I83_sync (bvand and5x4_sync S4x9_sync)) 
(Z7_sync (bvxor and0x7_sync S6x7_sync)) 
(C6x7_sync (bvor I91_sync I92_sync)) 
)
(let
(
(S6x8_sync (bvxor I93_sync C6x7_sync)) 
(S4x10_sync (bvxor I69_sync C4x9_sync)) 
(S5x9_sync (bvxor I81_sync C5x8_sync)) 
(I94_sync (bvand I93_sync C6x7_sync)) 
(I70_sync (bvand I69_sync C4x9_sync)) 
(I82_sync (bvand I81_sync C5x8_sync)) 
)
(let
(
(C4x10_sync (bvor I70_sync I71_sync)) 
(C6x8_sync (bvor I94_sync I95_sync)) 
(I96_sync (bvxor and4x5_sync S5x9_sync)) 
(I108_sync (bvxor and2x6_sync S6x8_sync)) 
(I110_sync (bvand and2x6_sync S6x8_sync)) 
(C5x9_sync (bvor I82_sync I83_sync)) 
(I86_sync (bvand and6x4_sync S4x10_sync)) 
(I98_sync (bvand and4x5_sync S5x9_sync)) 
(I84_sync (bvxor and6x4_sync S4x10_sync)) 
)
(let
(
(S6x9_sync (bvxor I96_sync C6x8_sync)) 
(S7x8_sync (bvxor I108_sync C7x7_sync)) 
(I97_sync (bvand I96_sync C6x8_sync)) 
(I89_sync (bvand and7x4_sync C4x10_sync)) 
(I109_sync (bvand I108_sync C7x7_sync)) 
(S5x10_sync (bvxor I84_sync C5x9_sync)) 
(I87_sync (bvxor and7x4_sync C4x10_sync)) 
(I85_sync (bvand I84_sync C5x9_sync)) 
)
(let
(
(C5x10_sync (bvor I85_sync I86_sync)) 
(C8x8_sync (bvand and1x7_sync S7x8_sync)) 
(C6x9_sync (bvor I97_sync I98_sync)) 
(Z8_sync (bvxor and1x7_sync S7x8_sync)) 
(I111_sync (bvxor and3x6_sync S6x9_sync)) 
(C7x8_sync (bvor I109_sync I110_sync)) 
(I99_sync (bvxor and5x5_sync S5x10_sync)) 
(I113_sync (bvand and3x6_sync S6x9_sync)) 
(I101_sync (bvand and5x5_sync S5x10_sync)) 
)
(let
(
(I112_sync (bvand I111_sync C7x8_sync)) 
(S7x9_sync (bvxor I111_sync C7x8_sync)) 
(I88_sync (bvand I87_sync C5x10_sync)) 
(S5x11_sync (bvxor I87_sync C5x10_sync)) 
(I100_sync (bvand I99_sync C6x9_sync)) 
(S6x10_sync (bvxor I99_sync C6x9_sync)) 
)
(let
(
(C5x11_sync (bvor I88_sync I89_sync)) 
(C6x10_sync (bvor I100_sync I101_sync)) 
(I126_sync (bvxor and2x7_sync S7x9_sync)) 
(I128_sync (bvand and2x7_sync S7x9_sync)) 
(I104_sync (bvand and6x5_sync S5x11_sync)) 
(C7x9_sync (bvor I112_sync I113_sync)) 
(I102_sync (bvxor and6x5_sync S5x11_sync)) 
(I114_sync (bvxor and4x6_sync S6x10_sync)) 
(I116_sync (bvand and4x6_sync S6x10_sync)) 
)
(let
(
(S7x10_sync (bvxor I114_sync C7x9_sync)) 
(Z9_sync (bvxor I126_sync C8x8_sync)) 
(I127_sync (bvand I126_sync C8x8_sync)) 
(I107_sync (bvand and7x5_sync C5x11_sync)) 
(I105_sync (bvxor and7x5_sync C5x11_sync)) 
(I115_sync (bvand I114_sync C7x9_sync)) 
(I103_sync (bvand I102_sync C6x10_sync)) 
(S6x11_sync (bvxor I102_sync C6x10_sync)) 
)
(let
(
(I119_sync (bvand and5x6_sync S6x11_sync)) 
(C6x11_sync (bvor I103_sync I104_sync)) 
(C7x10_sync (bvor I115_sync I116_sync)) 
(I131_sync (bvand and3x7_sync S7x10_sync)) 
(I129_sync (bvxor and3x7_sync S7x10_sync)) 
(C8x9_sync (bvor I127_sync I128_sync)) 
(I117_sync (bvxor and5x6_sync S6x11_sync)) 
)
(let
(
(S7x11_sync (bvxor I117_sync C7x10_sync)) 
(Z10_sync (bvxor I129_sync C8x9_sync)) 
(I118_sync (bvand I117_sync C7x10_sync)) 
(I130_sync (bvand I129_sync C8x9_sync)) 
(I106_sync (bvand I105_sync C6x11_sync)) 
(S6x12_sync (bvxor I105_sync C6x11_sync)) 
)
(let
(
(C8x10_sync (bvor I130_sync I131_sync)) 
(C7x11_sync (bvor I118_sync I119_sync)) 
(C6x12_sync (bvor I106_sync I107_sync)) 
(I120_sync (bvxor and6x6_sync S6x12_sync)) 
(I132_sync (bvxor and4x7_sync S7x11_sync)) 
(I122_sync (bvand and6x6_sync S6x12_sync)) 
(I134_sync (bvand and4x7_sync S7x11_sync)) 
)
(let
(
(S7x12_sync (bvxor I120_sync C7x11_sync)) 
(Z11_sync (bvxor I132_sync C8x10_sync)) 
(I133_sync (bvand I132_sync C8x10_sync)) 
(I121_sync (bvand I120_sync C7x11_sync)) 
(I123_sync (bvxor and7x6_sync C6x12_sync)) 
(I125_sync (bvand and7x6_sync C6x12_sync)) 
)
(let
(
(I137_sync (bvand and5x7_sync S7x12_sync)) 
(C7x12_sync (bvor I121_sync I122_sync)) 
(C8x11_sync (bvor I133_sync I134_sync)) 
(I135_sync (bvxor and5x7_sync S7x12_sync)) 
)
(let
(
(Z12_sync (bvxor I135_sync C8x11_sync)) 
(S7x13_sync (bvxor I123_sync C7x12_sync)) 
(I124_sync (bvand I123_sync C7x12_sync)) 
(I136_sync (bvand I135_sync C8x11_sync)) 
)
(let
(
(I138_sync (bvxor and6x7_sync S7x13_sync)) 
(I140_sync (bvand and6x7_sync S7x13_sync)) 
(C7x13_sync (bvor I124_sync I125_sync)) 
(C8x12_sync (bvor I136_sync I137_sync)) 
)
(let
(
(I143_sync (bvand and7x7_sync C7x13_sync)) 
(I139_sync (bvand I138_sync C8x12_sync)) 
(I141_sync (bvxor and7x7_sync C7x13_sync)) 
(Z13_sync (bvxor I138_sync C8x12_sync)) 
)
(let
(
(C8x13_sync (bvor I139_sync I140_sync)) 
)
(let
(
(I142_sync (bvand I141_sync C8x13_sync)) 
(Z14_sync (bvxor I141_sync C8x13_sync)) 
)
(let
(
(Z15_sync (bvor I142_sync I143_sync)) 
)
(=>
(and
(datap X0)
(datap X1)
(datap X2)
(datap X3)
(datap X4)
(datap X5)
(datap X6)
(datap X7)
(datap Y0)
(datap Y1)
(datap Y2)
(datap Y3)
(datap Y4)
(datap Y5)
(datap Y6)
(datap Y7)
(= (_ bv0 1) Gc_0)
)
(and
(= Z0_1 Z0_sync)
(= Z1_1 Z1_sync)
(= Z2_1 Z2_sync)
(= Z3_1 Z3_sync)
(= Z4_1 Z4_sync)
(= Z5_1 Z5_sync)
(= Z6_1 Z6_sync)
(= Z7_1 Z7_sync)
(= Z8_1 Z8_sync)
(= Z9_1 Z9_sync)
(= Z10_1 Z10_sync)
(= Z11_1 Z11_sync)
(= Z12_1 Z12_sync)
(= Z13_1 Z13_sync)
(= Z14_1 Z14_sync)
(= Z15_1 Z15_sync)
(not (= Z0_0 Z0_1))
(not (= Z1_0 Z1_1))
(not (= Z2_0 Z2_1))
(not (= Z3_0 Z3_1))
(not (= Z4_0 Z4_1))
(not (= Z5_0 Z5_1))
(not (= Z6_0 Z6_1))
(not (= Z7_0 Z7_1))
(not (= Z8_0 Z8_1))
(not (= Z9_0 Z9_1))
(not (= Z10_0 Z10_1))
(not (= Z11_0 Z11_1))
(not (= Z12_0 Z12_1))
(not (= Z13_0 Z13_1))
(not (= Z14_0 Z14_1))
(not (= Z15_0 Z15_1))
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
)
(check-sat)
(get-model)