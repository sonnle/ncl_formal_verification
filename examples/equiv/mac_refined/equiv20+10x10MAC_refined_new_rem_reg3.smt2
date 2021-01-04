(set-logic QF_BV)

(declare-fun Xi0 () (_ BitVec 2))
(declare-fun Xi1 () (_ BitVec 2))
(declare-fun Xi2 () (_ BitVec 2))
(declare-fun Xi3 () (_ BitVec 2))
(declare-fun Xi4 () (_ BitVec 2))
(declare-fun Xi5 () (_ BitVec 2))
(declare-fun Xi6 () (_ BitVec 2))
(declare-fun Xi7 () (_ BitVec 2))
(declare-fun Xi8 () (_ BitVec 2))
(declare-fun Xi9 () (_ BitVec 2))

(declare-fun Yi0 () (_ BitVec 2))
(declare-fun Yi1 () (_ BitVec 2))
(declare-fun Yi2 () (_ BitVec 2))
(declare-fun Yi3 () (_ BitVec 2))
(declare-fun Yi4 () (_ BitVec 2))
(declare-fun Yi5 () (_ BitVec 2))
(declare-fun Yi6 () (_ BitVec 2))
(declare-fun Yi7 () (_ BitVec 2))
(declare-fun Yi8 () (_ BitVec 2))
(declare-fun Yi9 () (_ BitVec 2))

(declare-fun ACCi0 () (_ BitVec 2))
(declare-fun ACCi1 () (_ BitVec 2))
(declare-fun ACCi2 () (_ BitVec 2))
(declare-fun ACCi3 () (_ BitVec 2))
(declare-fun ACCi4 () (_ BitVec 2))
(declare-fun ACCi5 () (_ BitVec 2))
(declare-fun ACCi6 () (_ BitVec 2))
(declare-fun ACCi7 () (_ BitVec 2))
(declare-fun ACCi8 () (_ BitVec 2))
(declare-fun ACCi9 () (_ BitVec 2))
(declare-fun ACCi10 () (_ BitVec 2))
(declare-fun ACCi11 () (_ BitVec 2))
(declare-fun ACCi12 () (_ BitVec 2))
(declare-fun ACCi13 () (_ BitVec 2))
(declare-fun ACCi14 () (_ BitVec 2))
(declare-fun ACCi15 () (_ BitVec 2))
(declare-fun ACCi16 () (_ BitVec 2))
(declare-fun ACCi17 () (_ BitVec 2))
(declare-fun ACCi18 () (_ BitVec 2))
(declare-fun ACCi19 () (_ BitVec 2))

(declare-fun RST () (_ BitVec 1))
(declare-fun Ki0 () (_ BitVec 1))
(declare-fun Ki1 () (_ BitVec 1))
(declare-fun Gc_0 () (_ BitVec 1))
(declare-fun CS0 () (_ BitVec 2))
(declare-fun CS1 () (_ BitVec 2))

; Extract Function of rail0 of a dual rail signal
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 0 0) a)
)

; Extract Function rail1 of a dual rail signal
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

; NCL Gate Dual Rail AND Logic
(define-fun and2_incomplete ((a (_ BitVec 2)) (b (_ BitVec 2)) (gl_1 (_ BitVec 1)) (gl_0 (_ BitVec 1))) (_ BitVec 2)
    (concat (th22 (rail1 a) (rail1 b) gl_1) (th12 (rail0 a) (rail0 b) gl_0))
)

; NCL Half-Adder
; The output will be concatenated as follows:        | variable - S1, S0, Cout1, Cout0
;                                                    |      bit -  3,  2,     1,     0
; The last gate values (gl) will be used as follows: | variable -      gl_3,      gl_2, gl_1, gl_0
;                                                    |     gate - th24comp0, th24comp1, th12, th22
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

; NCL reset-to-NULL register Function
(define-fun REG_NULL ((D (_ BitVec 2)) (Ki (_ BitVec 1)) (rst (_ BitVec 1)) (cs (_ BitVec 2))) (_ BitVec 2)
	(ite (= rst (_ bv0 1))
				(ite (= Ki (_ bv1 1)) D cs )
		(_ bv0 2)
	)
)

; NCL reset-to-DATA0 register Function
(define-fun REG_DATA0 ((D (_ BitVec 2)) (Ki (_ BitVec 1)) (rst (_ BitVec 1)) (cs (_ BitVec 2))) (_ BitVec 2)
	(ite (= rst (_ bv0 1))
				(ite (= Ki (_ bv1 1)) D cs )
		(_ bv1 2)
	)
)

; Synchronous reset-to-0 register Function
(define-fun REG0 ((D (_ BitVec 1)) (enable (_ BitVec 1)) (rst (_ BitVec 1)) (cs (_ BitVec 1))) (_ BitVec 1)
	(ite (= rst (_ bv0 1))
		(ite (= enable (_ bv1 1))
			D cs)
		(_ bv0 1)
	)
)

(assert
	(not
		(let
			(
				(X0_1 ((_ extract 1 1) Xi0))
				(X1_1 ((_ extract 1 1) Xi1))
				(X2_1 ((_ extract 1 1) Xi2))
				(X3_1 ((_ extract 1 1) Xi3))
				(X4_1 ((_ extract 1 1) Xi4))
				(X5_1 ((_ extract 1 1) Xi5))
				(X6_1 ((_ extract 1 1) Xi6))
				(X7_1 ((_ extract 1 1) Xi7))
				(X8_1 ((_ extract 1 1) Xi8))
				(X9_1 ((_ extract 1 1) Xi9))
				(Y0_1 ((_ extract 1 1) Yi0))
				(Y1_1 ((_ extract 1 1) Yi1))
				(Y2_1 ((_ extract 1 1) Yi2))
				(Y3_1 ((_ extract 1 1) Yi3))
				(Y4_1 ((_ extract 1 1) Yi4))
				(Y5_1 ((_ extract 1 1) Yi5))
				(Y6_1 ((_ extract 1 1) Yi6))
				(Y7_1 ((_ extract 1 1) Yi7))
				(Y8_1 ((_ extract 1 1) Yi8))
				(Y9_1 ((_ extract 1 1) Yi9))
				(ACC0_1 ((_ extract 1 1) ACCi0))
				(ACC1_1 ((_ extract 1 1) ACCi1))
				(ACC2_1 ((_ extract 1 1) ACCi2))
				(ACC3_1 ((_ extract 1 1) ACCi3))
				(ACC4_1 ((_ extract 1 1) ACCi4))
				(ACC5_1 ((_ extract 1 1) ACCi5))
				(ACC6_1 ((_ extract 1 1) ACCi6))
				(ACC7_1 ((_ extract 1 1) ACCi7))
				(ACC8_1 ((_ extract 1 1) ACCi8))
				(ACC9_1 ((_ extract 1 1) ACCi9))
				(ACC10_1 ((_ extract 1 1) ACCi10))
				(ACC11_1 ((_ extract 1 1) ACCi11))
				(ACC12_1 ((_ extract 1 1) ACCi12))
				(ACC13_1 ((_ extract 1 1) ACCi13))
				(ACC14_1 ((_ extract 1 1) ACCi14))
				(ACC15_1 ((_ extract 1 1) ACCi15))
				(ACC16_1 ((_ extract 1 1) ACCi16))
				(ACC17_1 ((_ extract 1 1) ACCi17))
				(ACC18_1 ((_ extract 1 1) ACCi18))
				(ACC19_1 ((_ extract 1 1) ACCi19))
			)
		(let
			(
				(X0 (concat X0_1 (bvnot X0_1)))
				(X1 (concat X1_1 (bvnot X1_1)))
				(X2 (concat X2_1 (bvnot X2_1)))
				(X3 (concat X3_1 (bvnot X3_1)))
				(X4 (concat X4_1 (bvnot X4_1)))
				(X5 (concat X5_1 (bvnot X5_1)))
				(X6 (concat X6_1 (bvnot X6_1)))
				(X7 (concat X7_1 (bvnot X7_1)))
				(X8 (concat X8_1 (bvnot X8_1)))
				(X9 (concat X9_1 (bvnot X9_1)))
				(Y0 (concat Y0_1 (bvnot Y0_1)))
				(Y1 (concat Y1_1 (bvnot Y1_1)))
				(Y2 (concat Y2_1 (bvnot Y2_1)))
				(Y3 (concat Y3_1 (bvnot Y3_1)))
				(Y4 (concat Y4_1 (bvnot Y4_1)))
				(Y5 (concat Y5_1 (bvnot Y5_1)))
				(Y6 (concat Y6_1 (bvnot Y6_1)))
				(Y7 (concat Y7_1 (bvnot Y7_1)))
				(Y8 (concat Y8_1 (bvnot Y8_1)))
				(Y9 (concat Y9_1 (bvnot Y9_1)))
				(ACC0 (concat ACC0_1 (bvnot ACC0_1)))
				(ACC1 (concat ACC1_1 (bvnot ACC1_1)))
				(ACC2 (concat ACC2_1 (bvnot ACC2_1)))
				(ACC3 (concat ACC3_1 (bvnot ACC3_1)))
				(ACC4 (concat ACC4_1 (bvnot ACC4_1)))
				(ACC5 (concat ACC5_1 (bvnot ACC5_1)))
				(ACC6 (concat ACC6_1 (bvnot ACC6_1)))
				(ACC7 (concat ACC7_1 (bvnot ACC7_1)))
				(ACC8 (concat ACC8_1 (bvnot ACC8_1)))
				(ACC9 (concat ACC9_1 (bvnot ACC9_1)))
				(ACC10 (concat ACC10_1 (bvnot ACC10_1)))
				(ACC11 (concat ACC11_1 (bvnot ACC11_1)))
				(ACC12 (concat ACC12_1 (bvnot ACC12_1)))
				(ACC13 (concat ACC13_1 (bvnot ACC13_1)))
				(ACC14 (concat ACC14_1 (bvnot ACC14_1)))
				(ACC15 (concat ACC15_1 (bvnot ACC15_1)))
				(ACC16 (concat ACC16_1 (bvnot ACC16_1)))
				(ACC17 (concat ACC17_1 (bvnot ACC17_1)))
				(ACC18 (concat ACC18_1 (bvnot ACC18_1)))
				(ACC19 (concat ACC19_1 (bvnot ACC19_1)))
			)
		(let
			(
				(and0x0_1 ((_ extract 1 1) (and2 X0 Y0 Gc_0 Gc_0)))
				(and0x1_1 ((_ extract 1 1) (and2_incomplete X0 Y1 Gc_0 Gc_0)))
				(and0x2_1 ((_ extract 1 1) (and2_incomplete X0 Y2 Gc_0 Gc_0)))
				(and0x3_1 ((_ extract 1 1) (and2_incomplete X0 Y3 Gc_0 Gc_0)))
				(and0x4_1 ((_ extract 1 1) (and2_incomplete X0 Y4 Gc_0 Gc_0)))
				(and0x5_1 ((_ extract 1 1) (and2_incomplete X0 Y5 Gc_0 Gc_0)))
				(and0x6_1 ((_ extract 1 1) (and2_incomplete X0 Y6 Gc_0 Gc_0)))
				(and0x7_1 ((_ extract 1 1) (and2_incomplete X0 Y7 Gc_0 Gc_0)))
				(and0x8_1 ((_ extract 1 1) (and2_incomplete X0 Y8 Gc_0 Gc_0)))
				(and0x9_1 ((_ extract 1 1) (and2_incomplete X0 Y9 Gc_0 Gc_0)))
				(and1x0_1 ((_ extract 1 1) (and2_incomplete X1 Y0 Gc_0 Gc_0)))
				(and1x1_1 ((_ extract 1 1) (and2 X1 Y1 Gc_0 Gc_0)))
				(and1x2_1 ((_ extract 1 1) (and2_incomplete X1 Y2 Gc_0 Gc_0)))
				(and1x3_1 ((_ extract 1 1) (and2_incomplete X1 Y3 Gc_0 Gc_0)))
				(and1x4_1 ((_ extract 1 1) (and2_incomplete X1 Y4 Gc_0 Gc_0)))
				(and1x5_1 ((_ extract 1 1) (and2_incomplete X1 Y5 Gc_0 Gc_0)))
				(and1x6_1 ((_ extract 1 1) (and2_incomplete X1 Y6 Gc_0 Gc_0)))
				(and1x7_1 ((_ extract 1 1) (and2_incomplete X1 Y7 Gc_0 Gc_0)))
				(and1x8_1 ((_ extract 1 1) (and2_incomplete X1 Y8 Gc_0 Gc_0)))
				(and1x9_1 ((_ extract 1 1) (and2_incomplete X1 Y9 Gc_0 Gc_0)))
				(and2x0_1 ((_ extract 1 1) (and2_incomplete X2 Y0 Gc_0 Gc_0)))
				(and2x1_1 ((_ extract 1 1) (and2_incomplete X2 Y1 Gc_0 Gc_0)))
				(and2x2_1 ((_ extract 1 1) (and2 X2 Y2 Gc_0 Gc_0)))
				(and2x3_1 ((_ extract 1 1) (and2_incomplete X2 Y3 Gc_0 Gc_0)))
				(and2x4_1 ((_ extract 1 1) (and2_incomplete X2 Y4 Gc_0 Gc_0)))
				(and2x5_1 ((_ extract 1 1) (and2_incomplete X2 Y5 Gc_0 Gc_0)))
				(and2x6_1 ((_ extract 1 1) (and2_incomplete X2 Y6 Gc_0 Gc_0)))
				(and2x7_1 ((_ extract 1 1) (and2_incomplete X2 Y7 Gc_0 Gc_0)))
				(and2x8_1 ((_ extract 1 1) (and2_incomplete X2 Y8 Gc_0 Gc_0)))
				(and2x9_1 ((_ extract 1 1) (and2_incomplete X2 Y9 Gc_0 Gc_0)))
				(and3x0_1 ((_ extract 1 1) (and2_incomplete X3 Y0 Gc_0 Gc_0)))
				(and3x1_1 ((_ extract 1 1) (and2_incomplete X3 Y1 Gc_0 Gc_0)))
				(and3x2_1 ((_ extract 1 1) (and2_incomplete X3 Y2 Gc_0 Gc_0)))
				(and3x3_1 ((_ extract 1 1) (and2 X3 Y3 Gc_0 Gc_0)))
				(and3x4_1 ((_ extract 1 1) (and2_incomplete X3 Y4 Gc_0 Gc_0)))
				(and3x5_1 ((_ extract 1 1) (and2_incomplete X3 Y5 Gc_0 Gc_0)))
				(and3x6_1 ((_ extract 1 1) (and2_incomplete X3 Y6 Gc_0 Gc_0)))
				(and3x7_1 ((_ extract 1 1) (and2_incomplete X3 Y7 Gc_0 Gc_0)))
				(and3x8_1 ((_ extract 1 1) (and2_incomplete X3 Y8 Gc_0 Gc_0)))
				(and3x9_1 ((_ extract 1 1) (and2_incomplete X3 Y9 Gc_0 Gc_0)))
				(and4x0_1 ((_ extract 1 1) (and2_incomplete X4 Y0 Gc_0 Gc_0)))
				(and4x1_1 ((_ extract 1 1) (and2_incomplete X4 Y1 Gc_0 Gc_0)))
				(and4x2_1 ((_ extract 1 1) (and2_incomplete X4 Y2 Gc_0 Gc_0)))
				(and4x3_1 ((_ extract 1 1) (and2_incomplete X4 Y3 Gc_0 Gc_0)))
				(and4x4_1 ((_ extract 1 1) (and2 X4 Y4 Gc_0 Gc_0)))
				(and4x5_1 ((_ extract 1 1) (and2_incomplete X4 Y5 Gc_0 Gc_0)))
				(and4x6_1 ((_ extract 1 1) (and2_incomplete X4 Y6 Gc_0 Gc_0)))
				(and4x7_1 ((_ extract 1 1) (and2_incomplete X4 Y7 Gc_0 Gc_0)))
				(and4x8_1 ((_ extract 1 1) (and2_incomplete X4 Y8 Gc_0 Gc_0)))
				(and4x9_1 ((_ extract 1 1) (and2_incomplete X4 Y9 Gc_0 Gc_0)))
				(and5x0_1 ((_ extract 1 1) (and2_incomplete X5 Y0 Gc_0 Gc_0)))
				(and5x1_1 ((_ extract 1 1) (and2_incomplete X5 Y1 Gc_0 Gc_0)))
				(and5x2_1 ((_ extract 1 1) (and2_incomplete X5 Y2 Gc_0 Gc_0)))
				(and5x3_1 ((_ extract 1 1) (and2_incomplete X5 Y3 Gc_0 Gc_0)))
				(and5x4_1 ((_ extract 1 1) (and2_incomplete X5 Y4 Gc_0 Gc_0)))
				(and5x5_1 ((_ extract 1 1) (and2 X5 Y5 Gc_0 Gc_0)))
				(and5x6_1 ((_ extract 1 1) (and2_incomplete X5 Y6 Gc_0 Gc_0)))
				(and5x7_1 ((_ extract 1 1) (and2_incomplete X5 Y7 Gc_0 Gc_0)))
				(and5x8_1 ((_ extract 1 1) (and2_incomplete X5 Y8 Gc_0 Gc_0)))
				(and5x9_1 ((_ extract 1 1) (and2_incomplete X5 Y9 Gc_0 Gc_0)))
				(and6x0_1 ((_ extract 1 1) (and2_incomplete X6 Y0 Gc_0 Gc_0)))
				(and6x1_1 ((_ extract 1 1) (and2_incomplete X6 Y1 Gc_0 Gc_0)))
				(and6x2_1 ((_ extract 1 1) (and2_incomplete X6 Y2 Gc_0 Gc_0)))
				(and6x3_1 ((_ extract 1 1) (and2_incomplete X6 Y3 Gc_0 Gc_0)))
				(and6x4_1 ((_ extract 1 1) (and2_incomplete X6 Y4 Gc_0 Gc_0)))
				(and6x5_1 ((_ extract 1 1) (and2_incomplete X6 Y5 Gc_0 Gc_0)))
				(and6x6_1 ((_ extract 1 1) (and2 X6 Y6 Gc_0 Gc_0)))
				(and6x7_1 ((_ extract 1 1) (and2_incomplete X6 Y7 Gc_0 Gc_0)))
				(and6x8_1 ((_ extract 1 1) (and2_incomplete X6 Y8 Gc_0 Gc_0)))
				(and6x9_1 ((_ extract 1 1) (and2_incomplete X6 Y9 Gc_0 Gc_0)))
				(and7x0_1 ((_ extract 1 1) (and2_incomplete X7 Y0 Gc_0 Gc_0)))
				(and7x1_1 ((_ extract 1 1) (and2_incomplete X7 Y1 Gc_0 Gc_0)))
				(and7x2_1 ((_ extract 1 1) (and2_incomplete X7 Y2 Gc_0 Gc_0)))
				(and7x3_1 ((_ extract 1 1) (and2_incomplete X7 Y3 Gc_0 Gc_0)))
				(and7x4_1 ((_ extract 1 1) (and2_incomplete X7 Y4 Gc_0 Gc_0)))
				(and7x5_1 ((_ extract 1 1) (and2_incomplete X7 Y5 Gc_0 Gc_0)))
				(and7x6_1 ((_ extract 1 1) (and2_incomplete X7 Y6 Gc_0 Gc_0)))
				(and7x7_1 ((_ extract 1 1) (and2 X7 Y7 Gc_0 Gc_0)))
				(and7x8_1 ((_ extract 1 1) (and2_incomplete X7 Y8 Gc_0 Gc_0)))
				(and7x9_1 ((_ extract 1 1) (and2_incomplete X7 Y9 Gc_0 Gc_0)))
				(and8x0_1 ((_ extract 1 1) (and2_incomplete X8 Y0 Gc_0 Gc_0)))
				(and8x1_1 ((_ extract 1 1) (and2_incomplete X8 Y1 Gc_0 Gc_0)))
				(and8x2_1 ((_ extract 1 1) (and2_incomplete X8 Y2 Gc_0 Gc_0)))
				(and8x3_1 ((_ extract 1 1) (and2_incomplete X8 Y3 Gc_0 Gc_0)))
				(and8x4_1 ((_ extract 1 1) (and2_incomplete X8 Y4 Gc_0 Gc_0)))
				(and8x5_1 ((_ extract 1 1) (and2_incomplete X8 Y5 Gc_0 Gc_0)))
				(and8x6_1 ((_ extract 1 1) (and2_incomplete X8 Y6 Gc_0 Gc_0)))
				(and8x7_1 ((_ extract 1 1) (and2_incomplete X8 Y7 Gc_0 Gc_0)))
				(and8x8_1 ((_ extract 1 1) (and2 X8 Y8 Gc_0 Gc_0)))
				(and8x9_1 ((_ extract 1 1) (and2_incomplete X8 Y9 Gc_0 Gc_0)))
				(and9x0_1 ((_ extract 1 1) (and2_incomplete X9 Y0 Gc_0 Gc_0)))
				(and9x1_1 ((_ extract 1 1) (and2_incomplete X9 Y1 Gc_0 Gc_0)))
				(and9x2_1 ((_ extract 1 1) (and2_incomplete X9 Y2 Gc_0 Gc_0)))
				(and9x3_1 ((_ extract 1 1) (and2_incomplete X9 Y3 Gc_0 Gc_0)))
				(and9x4_1 ((_ extract 1 1) (and2_incomplete X9 Y4 Gc_0 Gc_0)))
				(and9x5_1 ((_ extract 1 1) (and2_incomplete X9 Y5 Gc_0 Gc_0)))
				(and9x6_1 ((_ extract 1 1) (and2_incomplete X9 Y6 Gc_0 Gc_0)))
				(and9x7_1 ((_ extract 1 1) (and2_incomplete X9 Y7 Gc_0 Gc_0)))
				(and9x8_1 ((_ extract 1 1) (and2_incomplete X9 Y8 Gc_0 Gc_0)))
				(and9x9_1 ((_ extract 1 1) (and2 X9 Y9 Gc_0 Gc_0)))
			)
		(let
			(
				(and0x0 (concat and0x0_1 (bvnot and0x0_1)))
				(and0x1 (concat and0x1_1 (bvnot and0x1_1)))
				(and0x2 (concat and0x2_1 (bvnot and0x2_1)))
				(and0x3 (concat and0x3_1 (bvnot and0x3_1)))
				(and0x4 (concat and0x4_1 (bvnot and0x4_1)))
				(and0x5 (concat and0x5_1 (bvnot and0x5_1)))
				(and0x6 (concat and0x6_1 (bvnot and0x6_1)))
				(and0x7 (concat and0x7_1 (bvnot and0x7_1)))
				(and0x8 (concat and0x8_1 (bvnot and0x8_1)))
				(and0x9 (concat and0x9_1 (bvnot and0x9_1)))
				(and1x0 (concat and1x0_1 (bvnot and1x0_1)))
				(and1x1 (concat and1x1_1 (bvnot and1x1_1)))
				(and1x2 (concat and1x2_1 (bvnot and1x2_1)))
				(and1x3 (concat and1x3_1 (bvnot and1x3_1)))
				(and1x4 (concat and1x4_1 (bvnot and1x4_1)))
				(and1x5 (concat and1x5_1 (bvnot and1x5_1)))
				(and1x6 (concat and1x6_1 (bvnot and1x6_1)))
				(and1x7 (concat and1x7_1 (bvnot and1x7_1)))
				(and1x8 (concat and1x8_1 (bvnot and1x8_1)))
				(and1x9 (concat and1x9_1 (bvnot and1x9_1)))
				(and2x0 (concat and2x0_1 (bvnot and2x0_1)))
				(and2x1 (concat and2x1_1 (bvnot and2x1_1)))
				(and2x2 (concat and2x2_1 (bvnot and2x2_1)))
				(and2x3 (concat and2x3_1 (bvnot and2x3_1)))
				(and2x4 (concat and2x4_1 (bvnot and2x4_1)))
				(and2x5 (concat and2x5_1 (bvnot and2x5_1)))
				(and2x6 (concat and2x6_1 (bvnot and2x6_1)))
				(and2x7 (concat and2x7_1 (bvnot and2x7_1)))
				(and2x8 (concat and2x8_1 (bvnot and2x8_1)))
				(and2x9 (concat and2x9_1 (bvnot and2x9_1)))
				(and3x0 (concat and3x0_1 (bvnot and3x0_1)))
				(and3x1 (concat and3x1_1 (bvnot and3x1_1)))
				(and3x2 (concat and3x2_1 (bvnot and3x2_1)))
				(and3x3 (concat and3x3_1 (bvnot and3x3_1)))
				(and3x4 (concat and3x4_1 (bvnot and3x4_1)))
				(and3x5 (concat and3x5_1 (bvnot and3x5_1)))
				(and3x6 (concat and3x6_1 (bvnot and3x6_1)))
				(and3x7 (concat and3x7_1 (bvnot and3x7_1)))
				(and3x8 (concat and3x8_1 (bvnot and3x8_1)))
				(and3x9 (concat and3x9_1 (bvnot and3x9_1)))
				(and4x0 (concat and4x0_1 (bvnot and4x0_1)))
				(and4x1 (concat and4x1_1 (bvnot and4x1_1)))
				(and4x2 (concat and4x2_1 (bvnot and4x2_1)))
				(and4x3 (concat and4x3_1 (bvnot and4x3_1)))
				(and4x4 (concat and4x4_1 (bvnot and4x4_1)))
				(and4x5 (concat and4x5_1 (bvnot and4x5_1)))
				(and4x6 (concat and4x6_1 (bvnot and4x6_1)))
				(and4x7 (concat and4x7_1 (bvnot and4x7_1)))
				(and4x8 (concat and4x8_1 (bvnot and4x8_1)))
				(and4x9 (concat and4x9_1 (bvnot and4x9_1)))
				(and5x0 (concat and5x0_1 (bvnot and5x0_1)))
				(and5x1 (concat and5x1_1 (bvnot and5x1_1)))
				(and5x2 (concat and5x2_1 (bvnot and5x2_1)))
				(and5x3 (concat and5x3_1 (bvnot and5x3_1)))
				(and5x4 (concat and5x4_1 (bvnot and5x4_1)))
				(and5x5 (concat and5x5_1 (bvnot and5x5_1)))
				(and5x6 (concat and5x6_1 (bvnot and5x6_1)))
				(and5x7 (concat and5x7_1 (bvnot and5x7_1)))
				(and5x8 (concat and5x8_1 (bvnot and5x8_1)))
				(and5x9 (concat and5x9_1 (bvnot and5x9_1)))
				(and6x0 (concat and6x0_1 (bvnot and6x0_1)))
				(and6x1 (concat and6x1_1 (bvnot and6x1_1)))
				(and6x2 (concat and6x2_1 (bvnot and6x2_1)))
				(and6x3 (concat and6x3_1 (bvnot and6x3_1)))
				(and6x4 (concat and6x4_1 (bvnot and6x4_1)))
				(and6x5 (concat and6x5_1 (bvnot and6x5_1)))
				(and6x6 (concat and6x6_1 (bvnot and6x6_1)))
				(and6x7 (concat and6x7_1 (bvnot and6x7_1)))
				(and6x8 (concat and6x8_1 (bvnot and6x8_1)))
				(and6x9 (concat and6x9_1 (bvnot and6x9_1)))
				(and7x0 (concat and7x0_1 (bvnot and7x0_1)))
				(and7x1 (concat and7x1_1 (bvnot and7x1_1)))
				(and7x2 (concat and7x2_1 (bvnot and7x2_1)))
				(and7x3 (concat and7x3_1 (bvnot and7x3_1)))
				(and7x4 (concat and7x4_1 (bvnot and7x4_1)))
				(and7x5 (concat and7x5_1 (bvnot and7x5_1)))
				(and7x6 (concat and7x6_1 (bvnot and7x6_1)))
				(and7x7 (concat and7x7_1 (bvnot and7x7_1)))
				(and7x8 (concat and7x8_1 (bvnot and7x8_1)))
				(and7x9 (concat and7x9_1 (bvnot and7x9_1)))
				(and8x0 (concat and8x0_1 (bvnot and8x0_1)))
				(and8x1 (concat and8x1_1 (bvnot and8x1_1)))
				(and8x2 (concat and8x2_1 (bvnot and8x2_1)))
				(and8x3 (concat and8x3_1 (bvnot and8x3_1)))
				(and8x4 (concat and8x4_1 (bvnot and8x4_1)))
				(and8x5 (concat and8x5_1 (bvnot and8x5_1)))
				(and8x6 (concat and8x6_1 (bvnot and8x6_1)))
				(and8x7 (concat and8x7_1 (bvnot and8x7_1)))
				(and8x8 (concat and8x8_1 (bvnot and8x8_1)))
				(and8x9 (concat and8x9_1 (bvnot and8x9_1)))
				(and9x0 (concat and9x0_1 (bvnot and9x0_1)))
				(and9x1 (concat and9x1_1 (bvnot and9x1_1)))
				(and9x2 (concat and9x2_1 (bvnot and9x2_1)))
				(and9x3 (concat and9x3_1 (bvnot and9x3_1)))
				(and9x4 (concat and9x4_1 (bvnot and9x4_1)))
				(and9x5 (concat and9x5_1 (bvnot and9x5_1)))
				(and9x6 (concat and9x6_1 (bvnot and9x6_1)))
				(and9x7 (concat and9x7_1 (bvnot and9x7_1)))
				(and9x8 (concat and9x8_1 (bvnot and9x8_1)))
				(and9x9 (concat and9x9_1 (bvnot and9x9_1)))
			)
		(let
			(
				(S0x0 and0x0)
			)
		(let
			(
				(S1x1 ((_ extract 3 2) (ha and1x0 and0x1 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C1x1 ((_ extract 1 0) (ha and1x0 and0x1 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S1x2 ((_ extract 3 2) (fa and2x0 and1x1 C1x1 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C1x2 ((_ extract 1 0) (fa and2x0 and1x1 C1x1 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S1x3 ((_ extract 3 2) (fa and3x0 and2x1 C1x2 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C1x3 ((_ extract 1 0) (fa and3x0 and2x1 C1x2 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S1x4 ((_ extract 3 2) (fa and4x0 and3x1 C1x3 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C1x4 ((_ extract 1 0) (fa and4x0 and3x1 C1x3 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S1x5 ((_ extract 3 2) (fa and5x0 and4x1 C1x4 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C1x5 ((_ extract 1 0) (fa and5x0 and4x1 C1x4 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S1x6 ((_ extract 3 2) (fa and6x0 and5x1 C1x5 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C1x6 ((_ extract 1 0) (fa and6x0 and5x1 C1x5 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S1x7 ((_ extract 3 2) (fa and7x0 and6x1 C1x6 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C1x7 ((_ extract 1 0) (fa and7x0 and6x1 C1x6 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S1x8 ((_ extract 3 2) (fa and8x0 and7x1 C1x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C1x8 ((_ extract 1 0) (fa and8x0 and7x1 C1x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S1x9 ((_ extract 3 2) (fa and9x0 and8x1 C1x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C1x9 ((_ extract 1 0) (fa and9x0 and8x1 C1x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S2x2 ((_ extract 3 2) (ha and0x2 S1x2 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C2x2 ((_ extract 1 0) (ha and0x2 S1x2 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S2x3 ((_ extract 3 2) (fa and1x2 S1x3 C2x2 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C2x3 ((_ extract 1 0) (fa and1x2 S1x3 C2x2 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S2x4 ((_ extract 3 2) (fa and2x2 S1x4 C2x3 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C2x4 ((_ extract 1 0) (fa and2x2 S1x4 C2x3 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S2x5 ((_ extract 3 2) (fa and3x2 S1x5 C2x4 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C2x5 ((_ extract 1 0) (fa and3x2 S1x5 C2x4 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S2x6 ((_ extract 3 2) (fa and4x2 S1x6 C2x5 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C2x6 ((_ extract 1 0) (fa and4x2 S1x6 C2x5 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S2x7 ((_ extract 3 2) (fa and5x2 S1x7 C2x6 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C2x7 ((_ extract 1 0) (fa and5x2 S1x7 C2x6 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S2x8 ((_ extract 3 2) (fa and6x2 S1x8 C2x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C2x8 ((_ extract 1 0) (fa and6x2 S1x8 C2x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S2x9 ((_ extract 3 2) (fa and7x2 S1x9 C2x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C2x9 ((_ extract 1 0) (fa and7x2 S1x9 C2x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S2x10 ((_ extract 3 2) (fa and9x1 C1x9 C2x9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C2x10 ((_ extract 1 0) (fa and9x1 C1x9 C2x9 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S3x3 ((_ extract 3 2) (ha and0x3 S2x3 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C3x3 ((_ extract 1 0) (ha and0x3 S2x3 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S3x4 ((_ extract 3 2) (fa and1x3 S2x4 C3x3 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C3x4 ((_ extract 1 0) (fa and1x3 S2x4 C3x3 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S3x5 ((_ extract 3 2) (fa and2x3 S2x5 C3x4 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C3x5 ((_ extract 1 0) (fa and2x3 S2x5 C3x4 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S3x6 ((_ extract 3 2) (fa and3x3 S2x6 C3x5 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C3x6 ((_ extract 1 0) (fa and3x3 S2x6 C3x5 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S3x7 ((_ extract 3 2) (fa and4x3 S2x7 C3x6 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C3x7 ((_ extract 1 0) (fa and4x3 S2x7 C3x6 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S3x8 ((_ extract 3 2) (fa and5x3 S2x8 C3x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C3x8 ((_ extract 1 0) (fa and5x3 S2x8 C3x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S3x9 ((_ extract 3 2) (fa and6x3 S2x9 C3x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C3x9 ((_ extract 1 0) (fa and6x3 S2x9 C3x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S3x10 ((_ extract 3 2) (fa and8x2 S2x10 C3x9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C3x10 ((_ extract 1 0) (fa and8x2 S2x10 C3x9 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S3x11 ((_ extract 3 2) (fa and9x2 C2x10 C3x10 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C3x11 ((_ extract 1 0) (fa and9x2 C2x10 C3x10 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S4x4 ((_ extract 3 2) (ha and0x4 S3x4 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x4 ((_ extract 1 0) (ha and0x4 S3x4 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S4x5 ((_ extract 3 2) (fa and1x4 S3x5 C4x4 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x5 ((_ extract 1 0) (fa and1x4 S3x5 C4x4 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S4x6 ((_ extract 3 2) (fa and2x4 S3x6 C4x5 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x6 ((_ extract 1 0) (fa and2x4 S3x6 C4x5 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S4x7 ((_ extract 3 2) (fa and3x4 S3x7 C4x6 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x7 ((_ extract 1 0) (fa and3x4 S3x7 C4x6 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S4x8 ((_ extract 3 2) (fa and4x4 S3x8 C4x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x8 ((_ extract 1 0) (fa and4x4 S3x8 C4x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S4x9 ((_ extract 3 2) (fa and5x4 S3x9 C4x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x9 ((_ extract 1 0) (fa and5x4 S3x9 C4x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S4x10 ((_ extract 3 2) (fa and7x3 S3x10 C4x9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x10 ((_ extract 1 0) (fa and7x3 S3x10 C4x9 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S4x11 ((_ extract 3 2) (fa and8x3 S3x11 C4x10 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x11 ((_ extract 1 0) (fa and8x3 S3x11 C4x10 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S4x12 ((_ extract 3 2) (fa and9x3 C3x11 C4x11 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x12 ((_ extract 1 0) (fa and9x3 C3x11 C4x11 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x5 ((_ extract 3 2) (ha and0x5 S4x5 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x5 ((_ extract 1 0) (ha and0x5 S4x5 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x6 ((_ extract 3 2) (fa and1x5 S4x6 C5x5 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x6 ((_ extract 1 0) (fa and1x5 S4x6 C5x5 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x7 ((_ extract 3 2) (fa and2x5 S4x7 C5x6 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x7 ((_ extract 1 0) (fa and2x5 S4x7 C5x6 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x8 ((_ extract 3 2) (fa and3x5 S4x8 C5x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x8 ((_ extract 1 0) (fa and3x5 S4x8 C5x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x9 ((_ extract 3 2) (fa and4x5 S4x9 C5x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x9 ((_ extract 1 0) (fa and4x5 S4x9 C5x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x10 ((_ extract 3 2) (fa and6x4 S4x10 C5x9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x10 ((_ extract 1 0) (fa and6x4 S4x10 C5x9 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x11 ((_ extract 3 2) (fa and7x4 S4x11 C5x10 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x11 ((_ extract 1 0) (fa and7x4 S4x11 C5x10 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x12 ((_ extract 3 2) (fa and8x4 S4x12 C5x11 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x12 ((_ extract 1 0) (fa and8x4 S4x12 C5x11 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x13 ((_ extract 3 2) (fa and9x4 C4x12 C5x12 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x13 ((_ extract 1 0) (fa and9x4 C4x12 C5x12 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S6x6 ((_ extract 3 2) (ha and0x6 S5x6 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x6 ((_ extract 1 0) (ha and0x6 S5x6 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S6x7 ((_ extract 3 2) (fa and1x6 S5x7 C6x6 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x7 ((_ extract 1 0) (fa and1x6 S5x7 C6x6 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S6x8 ((_ extract 3 2) (fa and2x6 S5x8 C6x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x8 ((_ extract 1 0) (fa and2x6 S5x8 C6x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S6x9 ((_ extract 3 2) (fa and3x6 S5x9 C6x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x9 ((_ extract 1 0) (fa and3x6 S5x9 C6x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S6x10 ((_ extract 3 2) (fa and5x5 S5x10 C6x9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x10 ((_ extract 1 0) (fa and5x5 S5x10 C6x9 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S6x11 ((_ extract 3 2) (fa and6x5 S5x11 C6x10 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x11 ((_ extract 1 0) (fa and6x5 S5x11 C6x10 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S6x12 ((_ extract 3 2) (fa and7x5 S5x12 C6x11 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x12 ((_ extract 1 0) (fa and7x5 S5x12 C6x11 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S6x13 ((_ extract 3 2) (fa and8x5 S5x13 C6x12 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x13 ((_ extract 1 0) (fa and8x5 S5x13 C6x12 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S6x14 ((_ extract 3 2) (fa and9x5 C5x13 C6x13 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x14 ((_ extract 1 0) (fa and9x5 C5x13 C6x13 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x7 ((_ extract 3 2) (ha and0x7 S6x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x7 ((_ extract 1 0) (ha and0x7 S6x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x8 ((_ extract 3 2) (fa and1x7 S6x8 C7x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x8 ((_ extract 1 0) (fa and1x7 S6x8 C7x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x9 ((_ extract 3 2) (fa and2x7 S6x9 C7x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x9 ((_ extract 1 0) (fa and2x7 S6x9 C7x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x10 ((_ extract 3 2) (fa and4x6 S6x10 C7x9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x10 ((_ extract 1 0) (fa and4x6 S6x10 C7x9 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x11 ((_ extract 3 2) (fa and5x6 S6x11 C7x10 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x11 ((_ extract 1 0) (fa and5x6 S6x11 C7x10 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x12 ((_ extract 3 2) (fa and6x6 S6x12 C7x11 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x12 ((_ extract 1 0) (fa and6x6 S6x12 C7x11 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x13 ((_ extract 3 2) (fa and7x6 S6x13 C7x12 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x13 ((_ extract 1 0) (fa and7x6 S6x13 C7x12 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x14 ((_ extract 3 2) (fa and8x6 S6x14 C7x13 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x14 ((_ extract 1 0) (fa and8x6 S6x14 C7x13 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x15 ((_ extract 3 2) (fa and9x6 C6x14 C7x14 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x15 ((_ extract 1 0) (fa and9x6 C6x14 C7x14 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S8x8 ((_ extract 3 2) (ha and0x8 S7x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x8 ((_ extract 1 0) (ha and0x8 S7x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S8x9 ((_ extract 3 2) (fa and1x8 S7x9 C8x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x9 ((_ extract 1 0) (fa and1x8 S7x9 C8x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S8x10 ((_ extract 3 2) (fa and3x7 S7x10 C8x9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x10 ((_ extract 1 0) (fa and3x7 S7x10 C8x9 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S8x11 ((_ extract 3 2) (fa and4x7 S7x11 C8x10 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x11 ((_ extract 1 0) (fa and4x7 S7x11 C8x10 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S8x12 ((_ extract 3 2) (fa and5x7 S7x12 C8x11 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x12 ((_ extract 1 0) (fa and5x7 S7x12 C8x11 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S8x13 ((_ extract 3 2) (fa and6x7 S7x13 C8x12 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x13 ((_ extract 1 0) (fa and6x7 S7x13 C8x12 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S8x14 ((_ extract 3 2) (fa and7x7 S7x14 C8x13 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x14 ((_ extract 1 0) (fa and7x7 S7x14 C8x13 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S8x15 ((_ extract 3 2) (fa and8x7 S7x15 C8x14 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x15 ((_ extract 1 0) (fa and8x7 S7x15 C8x14 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S8x16 ((_ extract 3 2) (fa and9x7 C7x15 C8x15 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x16 ((_ extract 1 0) (fa and9x7 C7x15 C8x15 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S9x9 ((_ extract 3 2) (ha and0x9 S8x9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C9x9 ((_ extract 1 0) (ha and0x9 S8x9 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S9x10 ((_ extract 3 2) (fa and2x8 S8x10 C9x9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C9x10 ((_ extract 1 0) (fa and2x8 S8x10 C9x9 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S9x11 ((_ extract 3 2) (fa and3x8 S8x11 C9x10 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C9x11 ((_ extract 1 0) (fa and3x8 S8x11 C9x10 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S9x12 ((_ extract 3 2) (fa and4x8 S8x12 C9x11 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C9x12 ((_ extract 1 0) (fa and4x8 S8x12 C9x11 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S9x13 ((_ extract 3 2) (fa and5x8 S8x13 C9x12 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C9x13 ((_ extract 1 0) (fa and5x8 S8x13 C9x12 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S9x14 ((_ extract 3 2) (fa and6x8 S8x14 C9x13 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C9x14 ((_ extract 1 0) (fa and6x8 S8x14 C9x13 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S9x15 ((_ extract 3 2) (fa and7x8 S8x15 C9x14 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C9x15 ((_ extract 1 0) (fa and7x8 S8x15 C9x14 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S9x16 ((_ extract 3 2) (fa and8x8 S8x16 C9x15 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C9x16 ((_ extract 1 0) (fa and8x8 S8x16 C9x15 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S9x17 ((_ extract 3 2) (fa and9x8 C8x16 C9x16 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C9x17 ((_ extract 1 0) (fa and9x8 C8x16 C9x16 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S10x10 ((_ extract 3 2) (ha and1x9 S9x10 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C10x10 ((_ extract 1 0) (ha and1x9 S9x10 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S10x11 ((_ extract 3 2) (fa and2x9 S9x11 C10x10 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C10x11 ((_ extract 1 0) (fa and2x9 S9x11 C10x10 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S10x12 ((_ extract 3 2) (fa and3x9 S9x12 C10x11 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C10x12 ((_ extract 1 0) (fa and3x9 S9x12 C10x11 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S10x13 ((_ extract 3 2) (fa and4x9 S9x13 C10x12 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C10x13 ((_ extract 1 0) (fa and4x9 S9x13 C10x12 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S10x14 ((_ extract 3 2) (fa and5x9 S9x14 C10x13 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C10x14 ((_ extract 1 0) (fa and5x9 S9x14 C10x13 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S10x15 ((_ extract 3 2) (fa and6x9 S9x15 C10x14 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C10x15 ((_ extract 1 0) (fa and6x9 S9x15 C10x14 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S10x16 ((_ extract 3 2) (fa and7x9 S9x16 C10x15 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C10x16 ((_ extract 1 0) (fa and7x9 S9x16 C10x15 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S10x17 ((_ extract 3 2) (fa and8x9 S9x17 C10x16 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C10x17 ((_ extract 1 0) (fa and8x9 S9x17 C10x16 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S10x18 ((_ extract 3 2) (fa and9x9 C9x17 C10x17 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C10x18 ((_ extract 1 0) (fa and9x9 C9x17 C10x17 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(Z0_1 ((_ extract 1 1) S0x0))
				(Z1_1 ((_ extract 1 1) S1x1))
				(Z2_1 ((_ extract 1 1) S2x2))
				(Z3_1 ((_ extract 1 1) S3x3))
				(Z4_1 ((_ extract 1 1) S4x4))
				(Z5_1 ((_ extract 1 1) S5x5))
				(Z6_1 ((_ extract 1 1) S6x6))
				(Z7_1 ((_ extract 1 1) S7x7))
				(Z8_1 ((_ extract 1 1) S8x8))
				(Z9_1 ((_ extract 1 1) S9x9))
				(Z10_1 ((_ extract 1 1) S10x10))
				(Z11_1 ((_ extract 1 1) S10x11))
				(Z12_1 ((_ extract 1 1) S10x12))
				(Z13_1 ((_ extract 1 1) S10x13))
				(Z14_1 ((_ extract 1 1) S10x14))
				(Z15_1 ((_ extract 1 1) S10x15))
				(Z16_1 ((_ extract 1 1) S10x16))
				(Z17_1 ((_ extract 1 1) S10x17))
				(Z18_1 ((_ extract 1 1) S10x18))
				(Z19_1 ((_ extract 1 1) C10x18))
			)
		(let
			(
				(Z0 (concat Z0_1 (bvnot Z0_1)))
				(Z1 (concat Z1_1 (bvnot Z1_1)))
				(Z2 (concat Z2_1 (bvnot Z2_1)))
				(Z3 (concat Z3_1 (bvnot Z3_1)))
				(Z4 (concat Z4_1 (bvnot Z4_1)))
				(Z5 (concat Z5_1 (bvnot Z5_1)))
				(Z6 (concat Z6_1 (bvnot Z6_1)))
				(Z7 (concat Z7_1 (bvnot Z7_1)))
				(Z8 (concat Z8_1 (bvnot Z8_1)))
				(Z9 (concat Z9_1 (bvnot Z9_1)))
				(Z10 (concat Z10_1 (bvnot Z10_1)))
				(Z11 (concat Z11_1 (bvnot Z11_1)))
				(Z12 (concat Z12_1 (bvnot Z12_1)))
				(Z13 (concat Z13_1 (bvnot Z13_1)))
				(Z14 (concat Z14_1 (bvnot Z14_1)))
				(Z15 (concat Z15_1 (bvnot Z15_1)))
				(Z16 (concat Z16_1 (bvnot Z16_1)))
				(Z17 (concat Z17_1 (bvnot Z17_1)))
				(Z18 (concat Z18_1 (bvnot Z18_1)))
				(Z19 (concat Z19_1 (bvnot Z19_1)))
			)
        (let
			(
				(P0 ((_ extract 3 2) (ha ACC0 Z0 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA0 ((_ extract 1 0) (ha ACC0 Z0 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P1 ((_ extract 3 2) (fa ACC1 Z1 CA0 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA1 ((_ extract 1 0) (fa ACC1 Z1 CA0 Gc_0 Gc_0 Gc_0 Gc_0)))
        	)
		(let
			(
				(P2 ((_ extract 3 2) (fa ACC2 Z2 CA1 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA2 ((_ extract 1 0) (fa ACC2 Z2 CA1 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P3 ((_ extract 3 2) (fa ACC3 Z3 CA2 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA3 ((_ extract 1 0) (fa ACC3 Z3 CA2 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P4 ((_ extract 3 2) (fa ACC4 Z4 CA3 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA4 ((_ extract 1 0) (fa ACC4 Z4 CA3 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P5 ((_ extract 3 2) (fa ACC5 Z5 CA4 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA5 ((_ extract 1 0) (fa ACC5 Z5 CA4 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P6 ((_ extract 3 2) (fa ACC6 Z6 CA5 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA6 ((_ extract 1 0) (fa ACC6 Z6 CA5 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P7 ((_ extract 3 2) (fa ACC7 Z7 CA6 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA7 ((_ extract 1 0) (fa ACC7 Z7 CA6 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P8 ((_ extract 3 2) (fa ACC8 Z8 CA7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA8 ((_ extract 1 0) (fa ACC8 Z8 CA7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P9 ((_ extract 3 2) (fa ACC9 Z9 CA8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA9 ((_ extract 1 0) (fa ACC9 Z9 CA8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P10 ((_ extract 3 2) (fa ACC10 Z10 CA9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA10 ((_ extract 1 0) (fa ACC10 Z10 CA9 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P11 ((_ extract 3 2) (fa ACC11 Z11 CA10 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA11 ((_ extract 1 0) (fa ACC11 Z11 CA10 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P12 ((_ extract 3 2) (fa ACC12 Z12 CA11 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA12 ((_ extract 1 0) (fa ACC12 Z12 CA11 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P13 ((_ extract 3 2) (fa ACC13 Z13 CA12 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA13 ((_ extract 1 0) (fa ACC13 Z13 CA12 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P14 ((_ extract 3 2) (fa ACC14 Z14 CA13 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA14 ((_ extract 1 0) (fa ACC14 Z14 CA13 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P15 ((_ extract 3 2) (fa ACC15 Z15 CA14 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA15 ((_ extract 1 0) (fa ACC15 Z15 CA14 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P16 ((_ extract 3 2) (fa ACC16 Z16 CA15 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA16 ((_ extract 1 0) (fa ACC16 Z16 CA15 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P17 ((_ extract 3 2) (fa ACC17 Z17 CA16 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA17 ((_ extract 1 0) (fa ACC17 Z17 CA16 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P18 ((_ extract 3 2) (fa ACC18 Z18 CA17 Gc_0 Gc_0 Gc_0 Gc_0)))
				(CA18 ((_ extract 1 0) (fa ACC18 Z18 CA17 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(P19 ((_ extract 3 2) (fa ACC19 Z19 CA18 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
        (let
			(
				(ACCo0_1 ((_ extract 1 1) P0))
				(ACCo1_1 ((_ extract 1 1) P1))
				(ACCo2_1 ((_ extract 1 1) P2))
				(ACCo3_1 ((_ extract 1 1) P3))
				(ACCo4_1 ((_ extract 1 1) P4))
				(ACCo5_1 ((_ extract 1 1) P5))
				(ACCo6_1 ((_ extract 1 1) P6))
				(ACCo7_1 ((_ extract 1 1) P7))
				(ACCo8_1 ((_ extract 1 1) P8))
				(ACCo9_1 ((_ extract 1 1) P9))
				(ACCo10_1 ((_ extract 1 1) P10))
				(ACCo11_1 ((_ extract 1 1) P11))
				(ACCo12_1 ((_ extract 1 1) P12))
				(ACCo13_1 ((_ extract 1 1) P13))
				(ACCo14_1 ((_ extract 1 1) P14))
				(ACCo15_1 ((_ extract 1 1) P15))
				(ACCo16_1 ((_ extract 1 1) P16))
				(ACCo17_1 ((_ extract 1 1) P17))
				(ACCo18_1 ((_ extract 1 1) P18))
				(ACCo19_1 ((_ extract 1 1) P19))
			)
        (let
            (
                (ACCncl (concat ACCo19_1 ACCo18_1 ACCo17_1 ACCo16_1 ACCo15_1 ACCo14_1 ACCo13_1 ACCo12_1 ACCo11_1 ACCo10_1 ACCo9_1 ACCo8_1 ACCo7_1 ACCo6_1 ACCo5_1 ACCo4_1 ACCo3_1 ACCo2_1 ACCo1_1 ACCo0_1))
            )
        (let
			(
                (Psync (bvmul (concat (_ bv0 10) X9_1 X8_1 X7_1 X6_1 X5_1 X4_1 X3_1 X2_1 X1_1 X0_1) (concat (_ bv0 10) Y9_1 Y8_1 Y7_1 Y6_1 Y5_1 Y4_1 Y3_1 Y2_1 Y1_1 Y0_1)))
            )
        (let
            (
                (ACCsync (bvadd Psync (concat ACC19_1 ACC18_1 ACC17_1 ACC16_1 ACC15_1 ACC14_1 ACC13_1 ACC12_1 ACC11_1 ACC10_1 ACC9_1 ACC8_1 ACC7_1 ACC6_1 ACC5_1 ACC4_1 ACC3_1 ACC2_1 ACC1_1 ACC0_1)))
            )
        (=>
            (and
                (= (_ bv0 1) Gc_0)
                (datap Xi0)
				(datap Xi1)
				(datap Xi2)
				(datap Xi3)
				(datap Xi4)
				(datap Xi5)
				(datap Xi6)
				(datap Xi7)
				(datap Xi8)
				(datap Xi9)
				(datap Yi0)
				(datap Yi1)
				(datap Yi2)
				(datap Yi3)
				(datap Yi4)
				(datap Yi5)
				(datap Yi6)
				(datap Yi7)
				(datap Yi8)
				(datap Yi9)
				(datap ACCi0)
				(datap ACCi1)
				(datap ACCi2)
				(datap ACCi3)
				(datap ACCi4)
				(datap ACCi5)
				(datap ACCi6)
				(datap ACCi7)
				(datap ACCi8)
				(datap ACCi9)
				(datap ACCi10)
				(datap ACCi11)
				(datap ACCi12)
				(datap ACCi13)
				(datap ACCi14)
				(datap ACCi15)
				(datap ACCi16)
				(datap ACCi17)
				(datap ACCi18)
				(datap ACCi19)
            )
			(= ACCsync ACCncl)
        ))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    )
)

(check-sat)
(get-model)
