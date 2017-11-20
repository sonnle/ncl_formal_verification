; Formal verification proof - input completeness of ..\netlist_files\unsigned_mult_4x4.txt
(set-logic QF_BV)

; Inputs: Xa, Xb, Xc, Xd, Ya, Yb, Yc, Yd
(declare-fun Xa () (_ BitVec 2))
(declare-fun Xb () (_ BitVec 2))
(declare-fun Xc () (_ BitVec 2))
(declare-fun Xd () (_ BitVec 2))
(declare-fun Ya () (_ BitVec 2))
(declare-fun Yb () (_ BitVec 2))
(declare-fun Yc () (_ BitVec 2))
(declare-fun Yd () (_ BitVec 2))

; Outputs: Za, Zb, Zc, Zd, Ze, Zf, Zg, Zh
(declare-fun Za () (_ BitVec 2))
(declare-fun Zb () (_ BitVec 2))
(declare-fun Zc () (_ BitVec 2))
(declare-fun Zd () (_ BitVec 2))
(declare-fun Ze () (_ BitVec 2))
(declare-fun Zf () (_ BitVec 2))
(declare-fun Zg () (_ BitVec 2))
(declare-fun Zh () (_ BitVec 2))

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
(declare-fun Gc_42 () (_ BitVec 1))
(declare-fun Gc_43 () (_ BitVec 1))
(declare-fun Gc_44 () (_ BitVec 1))
(declare-fun Gc_45 () (_ BitVec 1))
(declare-fun Gc_46 () (_ BitVec 1))
(declare-fun Gc_47 () (_ BitVec 1))
(declare-fun Gc_48 () (_ BitVec 1))
(declare-fun Gc_49 () (_ BitVec 1))
(declare-fun Gc_50 () (_ BitVec 1))
(declare-fun Gc_51 () (_ BitVec 1))
(declare-fun Gc_52 () (_ BitVec 1))
(declare-fun Gc_53 () (_ BitVec 1))
(declare-fun Gc_54 () (_ BitVec 1))
(declare-fun Gc_55 () (_ BitVec 1))
(declare-fun Gc_56 () (_ BitVec 1))
(declare-fun Gc_57 () (_ BitVec 1))
(declare-fun Gc_58 () (_ BitVec 1))
(declare-fun Gc_59 () (_ BitVec 1))
(declare-fun Gc_60 () (_ BitVec 1))
(declare-fun Gc_61 () (_ BitVec 1))
(declare-fun Gc_62 () (_ BitVec 1))
(declare-fun Gc_63 () (_ BitVec 1))
(declare-fun Gc_64 () (_ BitVec 1))
(declare-fun Gc_65 () (_ BitVec 1))
(declare-fun Gc_66 () (_ BitVec 1))
(declare-fun Gc_67 () (_ BitVec 1))
(declare-fun Gc_68 () (_ BitVec 1))
(declare-fun Gc_69 () (_ BitVec 1))
(declare-fun Gc_70 () (_ BitVec 1))
(declare-fun Gc_71 () (_ BitVec 1))
(declare-fun Gc_72 () (_ BitVec 1))
(declare-fun Gc_73 () (_ BitVec 1))
(declare-fun Gc_74 () (_ BitVec 1))
(declare-fun Gc_75 () (_ BitVec 1))
(declare-fun Gc_76 () (_ BitVec 1))
(declare-fun Gc_77 () (_ BitVec 1))
(declare-fun Gc_78 () (_ BitVec 1))
(declare-fun Gc_79 () (_ BitVec 1))

; SAT/UNSAT assertion for ..\netlist_files\unsigned_mult_4x4.txt
(assert
    (not
        (let
            (
                (A0 (and Xa Ya Gc_0 Gc_1))
                (A1 (and Xa Yb Gc_2 Gc_3))
                (A2 (and Xb Ya Gc_4 Gc_5))
                (A3 (and Xb Yb Gc_10 Gc_11))
                (A4 (and Xc Ya Gc_12 Gc_13))
                (A5 (and Xd Ya Gc_18 Gc_19))
                (A6 (and Xc Yb Gc_20 Gc_21))
                (A7 (and Xa Yc Gc_26 Gc_27))
                (A8 (and Xb Yc Gc_32 Gc_33))
                (A9 (and Xd Yb Gc_38 Gc_39))
                (A10 (and Xa Yd Gc_44 Gc_45))
                (A11 (and Xc Yc Gc_50 Gc_51))
                (A12 (and Xd Yc Gc_56 Gc_57))
                (A13 (and Xb Yd Gc_62 Gc_63))
                (A14 (and Xc Yd Gc_68 Gc_69))
                (A15 (and Xd Yd Gc_74 Gc_75)))
        (let
            (
                (I1 A1)
                (I2 A2)
                (I4 A3)
                (I5 A4)
                (I2 A2)
                (I1 A1)
                (I2 A2)
                (I1 A1)
                (I2 A2)
        (let
            (
                (Gn_9 (ha Gc_1 Gc_2 Zb Gc_9))
                (Gn_17 (fa Gc_5 Gc_4 Gc_3 Gc_6 Gc_17))
                (Gn_25 (fa Gc_9 Gc_8 Gc_7 Gc_10 Gc_25)))
        (let
            (
                (Gn_31 (ha Gc_6 Gc_12 Zc Gc_31))
                (Gn_37 (fa Gc_10 Gc_14 Gc_13 Gc_15 Gc_37))
                (Gn_43 (fa Gc_17 Gc_11 Gc_16 Gc_18 Gc_43)))
        (let
            (
                (Gn_49 (ha Gc_15 Gc_20 Zd Gc_49))
                (Gn_55 (fa Gc_18 Gc_22 Gc_21 Gc_23 Gc_55))
                (Gn_61 (fa Gc_25 Gc_19 Gc_24 Gc_26 Gc_61)))
        (let
            (
                (Gn_67 (ha Gc_23 Gc_28 Ze Gc_67))
                (Gn_73 (fa Gc_26 Gc_30 Gc_29 Zf Gc_73))
                (Gn_79 (fa Gc_32 Gc_27 Gc_31 Zg Gc_79)))
        (let
            (
                (Za (concat Gn_h Gn_Z))
                (Zb (concat Gn_h Gn_Z))
                (Zc (concat Gn_h Gn_Z))
                (Zd (concat Gn_h Gn_Z))
                (Ze (concat Gn_h Gn_Z))
                (Zf (concat Gn_h Gn_Z))
                (Zg (concat Gn_h Gn_Z))
                (Zh (concat Gn_h Gn_Z)))
        (=>
            (and
                (not (= (_ bv3 2) Xa))
                (not (= (_ bv3 2) Xb))
                (not (= (_ bv3 2) Xc))
                (not (= (_ bv3 2) Xd))
                (not (= (_ bv3 2) Ya))
                (not (= (_ bv3 2) Yb))
                (not (= (_ bv3 2) Yc))
                (not (= (_ bv3 2) Yd))
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
                (= (_ bv0 1) Gc_42)
                (= (_ bv0 1) Gc_43)
                (= (_ bv0 1) Gc_44)
                (= (_ bv0 1) Gc_45)
                (= (_ bv0 1) Gc_46)
                (= (_ bv0 1) Gc_47)
                (= (_ bv0 1) Gc_48)
                (= (_ bv0 1) Gc_49)
                (= (_ bv0 1) Gc_50)
                (= (_ bv0 1) Gc_51)
                (= (_ bv0 1) Gc_52)
                (= (_ bv0 1) Gc_53)
                (= (_ bv0 1) Gc_54)
                (= (_ bv0 1) Gc_55)
                (= (_ bv0 1) Gc_56)
                (= (_ bv0 1) Gc_57)
                (= (_ bv0 1) Gc_58)
                (= (_ bv0 1) Gc_59)
                (= (_ bv0 1) Gc_60)
                (= (_ bv0 1) Gc_61)
                (= (_ bv0 1) Gc_62)
                (= (_ bv0 1) Gc_63)
                (= (_ bv0 1) Gc_64)
                (= (_ bv0 1) Gc_65)
                (= (_ bv0 1) Gc_66)
                (= (_ bv0 1) Gc_67)
                (= (_ bv0 1) Gc_68)
                (= (_ bv0 1) Gc_69)
                (= (_ bv0 1) Gc_70)
                (= (_ bv0 1) Gc_71)
                (= (_ bv0 1) Gc_72)
                (= (_ bv0 1) Gc_73)
                (= (_ bv0 1) Gc_74)
                (= (_ bv0 1) Gc_75)
                (= (_ bv0 1) Gc_76)
                (= (_ bv0 1) Gc_77)
                (= (_ bv0 1) Gc_78)
                (= (_ bv0 1) Gc_79)
                (or
                    (nullp Xa)
                    (nullp Xb)
                    (nullp Xc)
                    (nullp Xd)
                    (nullp Ya)
                    (nullp Yb)
                    (nullp Yc)
                    (nullp Yd)))
            (or
                (nullp Za)
                (nullp Zb)
                (nullp Zc)
                (nullp Zd)
                (nullp Ze)
                (nullp Zf)
                (nullp Zg)
                (nullp Zh)))))))))
    )
)

(check-sat)
(get-model)
