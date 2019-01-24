(set-logic QF_BV)
; Inputs: X0 X1 X2 X3 Y0 Y1 Y2 Y3
(declare-fun X0 () (_ BitVec 2))
(declare-fun X1 () (_ BitVec 2))
(declare-fun X2 () (_ BitVec 2))
(declare-fun X3 () (_ BitVec 2))
(declare-fun Y0 () (_ BitVec 2))
(declare-fun Y1 () (_ BitVec 2))
(declare-fun Y2 () (_ BitVec 2))
(declare-fun Y3 () (_ BitVec 2))
; Outputs: Z0 Z1 Z2 Z3 Z4 Z5 Z6 Z7
(declare-fun Z0 () (_ BitVec 2))
(declare-fun Z1 () (_ BitVec 2))
(declare-fun Z2 () (_ BitVec 2))
(declare-fun Z3 () (_ BitVec 2))
(declare-fun Z4 () (_ BitVec 2))
(declare-fun Z5 () (_ BitVec 2))
(declare-fun Z6 () (_ BitVec 2))
(declare-fun Z7 () (_ BitVec 2))
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
(and0x2_0 (th12 (rail0 X0) (rail0 Y2) Gc_0))
(and0x2_1 (th22 (rail1 X0) (rail1 Y2) Gc_0))
(and2x3_1 (th22 (rail1 X2) (rail1 Y3) Gc_0))
(and2x3_0 (th12 (rail0 X2) (rail0 Y3) Gc_0))
(and2x2_0 (thand0 (rail0 Y2) (rail0 X2) (rail1 Y2) (rail1 X2) Gc_0))
(and2x2_1 (th22 (rail1 X2) (rail1 Y2) Gc_0))
(and2x1_1 (th22 (rail1 X2) (rail1 Y1) Gc_0))
(and2x1_0 (th12 (rail0 X2) (rail0 Y1) Gc_0))
(and0x1_1 (th22 (rail1 X0) (rail1 Y1) Gc_0))
(and0x1_0 (th12 (rail0 X0) (rail0 Y1) Gc_0))
(and0x3_1 (th22 (rail1 X0) (rail1 Y3) Gc_0))
(and0x3_0 (th12 (rail0 X0) (rail0 Y3) Gc_0))
(and2x0_0 (th12 (rail0 X2) (rail0 Y0) Gc_0))
(and3x0_0 (th12 (rail0 X3) (rail0 Y0) Gc_0))
(and3x2_1 (th22 (rail1 X3) (rail1 Y2) Gc_0))
(and3x2_0 (th12 (rail0 X3) (rail0 Y2) Gc_0))
(Z0_1 (th22 (rail1 X0) (rail1 Y0) Gc_0))
(Z0_0 (thand0 (rail0 Y0) (rail0 X0) (rail1 Y0) (rail1 X0) Gc_0))
(and3x3_0 (thand0 (rail0 Y3) (rail0 X3) (rail1 Y3) (rail1 X3) Gc_0))
(and3x3_1 (th22 (rail1 X3) (rail1 Y3) Gc_0))
(and3x0_1 (th22 (rail1 X3) (rail1 Y0) Gc_0))
(and2x0_1 (th22 (rail1 X2) (rail1 Y0) Gc_0))
(and1x0_1 (th22 (rail1 X1) (rail1 Y0) Gc_0))
(and1x0_0 (th12 (rail0 X1) (rail0 Y0) Gc_0))
(and3x1_0 (th12 (rail0 X3) (rail0 Y1) Gc_0))
(and3x1_1 (th22 (rail1 X3) (rail1 Y1) Gc_0))
(and1x1_0 (thand0 (rail0 Y1) (rail0 X1) (rail1 Y1) (rail1 X1) Gc_0))
(and1x1_1 (th22 (rail1 X1) (rail1 Y1) Gc_0))
(and1x2_1 (th22 (rail1 X1) (rail1 Y2) Gc_0))
(and1x2_0 (th12 (rail0 X1) (rail0 Y2) Gc_0))
(and1x3_0 (th12 (rail0 X1) (rail0 Y3) Gc_0))
(and1x3_1 (th22 (rail1 X1) (rail1 Y3) Gc_0))
)
(let
(
(Z1_1 (th24comp and0x1_0 and1x0_0 and0x1_1 and1x0_1 Gc_0))
(C1x1_0 (th12 and0x1_0 and1x0_0 Gc_0))
(C1x1_1 (th22 and0x1_1 and1x0_1 Gc_0))
(Z1_0 (th24comp and0x1_0 and1x0_1 and1x0_0 and0x1_1 Gc_0))
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
(Z2_1 (th24comp S1x2_0 and0x2_0 S1x2_1 and0x2_1 Gc_0))
(Z2_0 (th24comp S1x2_0 and0x2_1 and0x2_0 S1x2_1 Gc_0))
(C2x2_0 (th12 S1x2_0 and0x2_0 Gc_0))
(C2x2_1 (th22 S1x2_1 and0x2_1 Gc_0))
)
(let
(
(C2x3_1 (th23 and1x2_1 S1x3_1 C2x2_1 Gc_0))
(C2x3_0 (th23 and1x2_0 S1x3_0 C2x2_0 Gc_0))
)
(let
(
(C2x4_0 (th23 and3x1_0 C1x3_0 C2x3_0 Gc_0))
(C2x4_1 (th23 and3x1_1 C1x3_1 C2x3_1 Gc_0))
(S2x3_1 (th34w2 C2x3_0 and1x2_1 S1x3_1 C2x2_1 Gc_0))
(S2x3_0 (th34w2 C2x3_1 and1x2_0 S1x3_0 C2x2_0 Gc_0))
)
(let
(
(Z3_0 (th24comp S2x3_0 and0x3_1 and0x3_0 S2x3_1 Gc_0))
(Z3_1 (th24comp S2x3_0 and0x3_0 S2x3_1 and0x3_1 Gc_0))
(S2x4_0 (th34w2 C2x4_1 and3x1_0 C1x3_0 C2x3_0 Gc_0))
(S2x4_1 (th34w2 C2x4_0 and3x1_1 C1x3_1 C2x3_1 Gc_0))
(C3x3_0 (th12 S2x3_0 and0x3_0 Gc_0))
(C3x3_1 (th22 S2x3_1 and0x3_1 Gc_0))
)
(let
(
(C3x4_1 (th23 and2x2_1 S2x4_1 C3x3_1 Gc_0))
(C3x4_0 (th23 and2x2_0 S2x4_0 C3x3_0 Gc_0))
)
(let
(
(S3x4_1 (th34w2 C3x4_0 and2x2_1 S2x4_1 C3x3_1 Gc_0))
(S3x4_0 (th34w2 C3x4_1 and2x2_0 S2x4_0 C3x3_0 Gc_0))
(C3x5_0 (th23 and3x2_0 C2x4_0 C3x4_0 Gc_0))
(C3x5_1 (th23 and3x2_1 C2x4_1 C3x4_1 Gc_0))
)
(let
(
(Z4_1 (th24comp S3x4_0 and1x3_0 S3x4_1 and1x3_1 Gc_0))
(Z4_0 (th24comp S3x4_0 and1x3_1 and1x3_0 S3x4_1 Gc_0))
(S3x5_0 (th34w2 C3x5_1 and3x2_0 C2x4_0 C3x4_0 Gc_0))
(S3x5_1 (th34w2 C3x5_0 and3x2_1 C2x4_1 C3x4_1 Gc_0))
(C4x4_0 (th12 S3x4_0 and1x3_0 Gc_0))
(C4x4_1 (th22 S3x4_1 and1x3_1 Gc_0))
)
(let
(
(C4x5_1 (th23 and2x3_1 S3x5_1 C4x4_1 Gc_0))
(C4x5_0 (th23 and2x3_0 S3x5_0 C4x4_0 Gc_0))
)
(let
(
(Z7_0 (th23 and3x3_0 C3x5_0 C4x5_0 Gc_0))
(Z7_1 (th23 and3x3_1 C3x5_1 C4x5_1 Gc_0))
(Z5_0 (th34w2 C4x5_1 and2x3_0 S3x5_0 C4x4_0 Gc_0))
(Z5_1 (th34w2 C4x5_0 and2x3_1 S3x5_1 C4x4_1 Gc_0))
)
(let
(
(Z6_1 (th34w2 Z7_0 and3x3_1 C3x5_1 C4x5_1 Gc_0))
(Z6_0 (th34w2 Z7_1 and3x3_0 C3x5_0 C4x5_0 Gc_0))
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
)
(let
(
(and1x2_sync (bvand (rail1 X1) (rail1 Y2))) 
(and1x3_sync (bvand (rail1 X1) (rail1 Y3))) 
(and1x0_sync (bvand (rail1 X1) (rail1 Y0))) 
(and1x1_sync (bvand (rail1 X1) (rail1 Y1))) 
(and2x1_sync (bvand (rail1 X2) (rail1 Y1))) 
(and0x3_sync (bvand (rail1 X0) (rail1 Y3))) 
(and0x2_sync (bvand (rail1 X0) (rail1 Y2))) 
(and0x1_sync (bvand (rail1 X0) (rail1 Y1))) 
(and2x0_sync (bvand (rail1 X2) (rail1 Y0))) 
(and3x0_sync (bvand (rail1 X3) (rail1 Y0))) 
(and2x3_sync (bvand (rail1 X2) (rail1 Y3))) 
(and3x2_sync (bvand (rail1 X3) (rail1 Y2))) 
(and3x3_sync (bvand (rail1 X3) (rail1 Y3))) 
(and2x2_sync (bvand (rail1 X2) (rail1 Y2))) 
(Z0_sync (bvand (rail1 X0) (rail1 Y0))) 
(and3x1_sync (bvand (rail1 X3) (rail1 Y1))) 
)
(let
(
(C1x1_sync (bvand and1x0_sync and0x1_sync)) 
(I0_sync (bvxor and2x0_sync and1x1_sync)) 
(I3_sync (bvxor and3x0_sync and2x1_sync)) 
(I2_sync (bvand and2x0_sync and1x1_sync)) 
(I5_sync (bvand and3x0_sync and2x1_sync)) 
(Z1_sync (bvxor and1x0_sync and0x1_sync)) 
)
(let
(
(I1_sync (bvand I0_sync C1x1_sync)) 
(S1x2_sync (bvxor I0_sync C1x1_sync)) 
)
(let
(
(C1x2_sync (bvor I1_sync I2_sync)) 
(Z2_sync (bvxor and0x2_sync S1x2_sync)) 
(C2x2_sync (bvand and0x2_sync S1x2_sync)) 
)
(let
(
(I4_sync (bvand I3_sync C1x2_sync)) 
(S1x3_sync (bvxor I3_sync C1x2_sync)) 
)
(let
(
(I8_sync (bvand and1x2_sync S1x3_sync)) 
(C1x3_sync (bvor I4_sync I5_sync)) 
(I6_sync (bvxor and1x2_sync S1x3_sync)) 
)
(let
(
(I9_sync (bvxor and3x1_sync C1x3_sync)) 
(S2x3_sync (bvxor I6_sync C2x2_sync)) 
(I11_sync (bvand and3x1_sync C1x3_sync)) 
(I7_sync (bvand I6_sync C2x2_sync)) 
)
(let
(
(C2x3_sync (bvor I7_sync I8_sync)) 
(C3x3_sync (bvand and0x3_sync S2x3_sync)) 
(Z3_sync (bvxor and0x3_sync S2x3_sync)) 
)
(let
(
(S2x4_sync (bvxor I9_sync C2x3_sync)) 
(I10_sync (bvand I9_sync C2x3_sync)) 
)
(let
(
(I14_sync (bvand and2x2_sync S2x4_sync)) 
(C2x4_sync (bvor I10_sync I11_sync)) 
(I12_sync (bvxor and2x2_sync S2x4_sync)) 
)
(let
(
(I15_sync (bvxor and3x2_sync C2x4_sync)) 
(S3x4_sync (bvxor I12_sync C3x3_sync)) 
(I17_sync (bvand and3x2_sync C2x4_sync)) 
(I13_sync (bvand I12_sync C3x3_sync)) 
)
(let
(
(Z4_sync (bvxor and1x3_sync S3x4_sync)) 
(C3x4_sync (bvor I13_sync I14_sync)) 
(C4x4_sync (bvand and1x3_sync S3x4_sync)) 
)
(let
(
(I16_sync (bvand I15_sync C3x4_sync)) 
(S3x5_sync (bvxor I15_sync C3x4_sync)) 
)
(let
(
(I20_sync (bvand and2x3_sync S3x5_sync)) 
(C3x5_sync (bvor I16_sync I17_sync)) 
(I18_sync (bvxor and2x3_sync S3x5_sync)) 
)
(let
(
(I21_sync (bvxor and3x3_sync C3x5_sync)) 
(I23_sync (bvand and3x3_sync C3x5_sync)) 
(I19_sync (bvand I18_sync C4x4_sync)) 
(Z5_sync (bvxor I18_sync C4x4_sync)) 
)
(let
(
(C4x5_sync (bvor I19_sync I20_sync)) 
)
(let
(
(I22_sync (bvand I21_sync C4x5_sync)) 
(Z6_sync (bvxor I21_sync C4x5_sync)) 
)
(let
(
(Z7_sync (bvor I22_sync I23_sync)) 
)
(=>
(and
(datap X0)
(datap X1)
(datap X2)
(datap X3)
(datap Y0)
(datap Y1)
(datap Y2)
(datap Y3)
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
(not (= Z0_0 Z0_1))
(not (= Z1_0 Z1_1))
(not (= Z2_0 Z2_1))
(not (= Z3_0 Z3_1))
(not (= Z4_0 Z4_1))
(not (= Z5_0 Z5_1))
(not (= Z6_0 Z6_1))
(not (= Z7_0 Z7_1))
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