(set-logic QF_BV)

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

(declare-fun ACC0 () (_ BitVec 2))
(declare-fun ACC1 () (_ BitVec 2))
(declare-fun ACC2 () (_ BitVec 2))
(declare-fun ACC3 () (_ BitVec 2))
(declare-fun ACC4 () (_ BitVec 2))
(declare-fun ACC5 () (_ BitVec 2))
(declare-fun ACC6 () (_ BitVec 2))
(declare-fun ACC7 () (_ BitVec 2))
(declare-fun ACC8 () (_ BitVec 2))
(declare-fun ACC9 () (_ BitVec 2))
(declare-fun ACC10 () (_ BitVec 2))
(declare-fun ACC11 () (_ BitVec 2))
(declare-fun ACC12 () (_ BitVec 2))
(declare-fun ACC13 () (_ BitVec 2))
(declare-fun ACC14 () (_ BitVec 2))
(declare-fun ACC15 () (_ BitVec 2))

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
				(and0x0 (and2 X0 Y0 Gc_0 Gc_0))
				(and0x1 (and2_incomplete X0 Y1 Gc_0 Gc_0))
				(and0x2 (and2_incomplete X0 Y2 Gc_0 Gc_0))
				(and0x3 (and2_incomplete X0 Y3 Gc_0 Gc_0))
				(and0x4 (and2_incomplete X0 Y4 Gc_0 Gc_0))
				(and0x5 (and2_incomplete X0 Y5 Gc_0 Gc_0))
				(and0x6 (and2_incomplete X0 Y6 Gc_0 Gc_0))
				(and0x7 (and2_incomplete X0 Y7 Gc_0 Gc_0))
				(and1x0 (and2_incomplete X1 Y0 Gc_0 Gc_0))
				(and1x1 (and2 X1 Y1 Gc_0 Gc_0))
				(and1x2 (and2_incomplete X1 Y2 Gc_0 Gc_0))
				(and1x3 (and2_incomplete X1 Y3 Gc_0 Gc_0))
				(and1x4 (and2_incomplete X1 Y4 Gc_0 Gc_0))
				(and1x5 (and2_incomplete X1 Y5 Gc_0 Gc_0))
				(and1x6 (and2_incomplete X1 Y6 Gc_0 Gc_0))
				(and1x7 (and2_incomplete X1 Y7 Gc_0 Gc_0))
				(and2x0 (and2_incomplete X2 Y0 Gc_0 Gc_0))
				(and2x1 (and2_incomplete X2 Y1 Gc_0 Gc_0))
				(and2x2 (and2 X2 Y2 Gc_0 Gc_0))
				(and2x3 (and2_incomplete X2 Y3 Gc_0 Gc_0))
				(and2x4 (and2_incomplete X2 Y4 Gc_0 Gc_0))
				(and2x5 (and2_incomplete X2 Y5 Gc_0 Gc_0))
				(and2x6 (and2_incomplete X2 Y6 Gc_0 Gc_0))
				(and2x7 (and2_incomplete X2 Y7 Gc_0 Gc_0))
				(and3x0 (and2_incomplete X3 Y0 Gc_0 Gc_0))
				(and3x1 (and2_incomplete X3 Y1 Gc_0 Gc_0))
				(and3x2 (and2_incomplete X3 Y2 Gc_0 Gc_0))
				(and3x3 (and2 X3 Y3 Gc_0 Gc_0))
				(and3x4 (and2_incomplete X3 Y4 Gc_0 Gc_0))
				(and3x5 (and2_incomplete X3 Y5 Gc_0 Gc_0))
				(and3x6 (and2_incomplete X3 Y6 Gc_0 Gc_0))
				(and3x7 (and2_incomplete X3 Y7 Gc_0 Gc_0))
				(and4x0 (and2_incomplete X4 Y0 Gc_0 Gc_0))
				(and4x1 (and2_incomplete X4 Y1 Gc_0 Gc_0))
				(and4x2 (and2_incomplete X4 Y2 Gc_0 Gc_0))
				(and4x3 (and2_incomplete X4 Y3 Gc_0 Gc_0))
				(and4x4 (and2 X4 Y4 Gc_0 Gc_0))
				(and4x5 (and2_incomplete X4 Y5 Gc_0 Gc_0))
				(and4x6 (and2_incomplete X4 Y6 Gc_0 Gc_0))
				(and4x7 (and2_incomplete X4 Y7 Gc_0 Gc_0))
				(and5x0 (and2_incomplete X5 Y0 Gc_0 Gc_0))
				(and5x1 (and2_incomplete X5 Y1 Gc_0 Gc_0))
				(and5x2 (and2_incomplete X5 Y2 Gc_0 Gc_0))
				(and5x3 (and2_incomplete X5 Y3 Gc_0 Gc_0))
				(and5x4 (and2_incomplete X5 Y4 Gc_0 Gc_0))
				(and5x5 (and2 X5 Y5 Gc_0 Gc_0))
				(and5x6 (and2_incomplete X5 Y6 Gc_0 Gc_0))
				(and5x7 (and2_incomplete X5 Y7 Gc_0 Gc_0))
				(and6x0 (and2_incomplete X6 Y0 Gc_0 Gc_0))
				(and6x1 (and2_incomplete X6 Y1 Gc_0 Gc_0))
				(and6x2 (and2_incomplete X6 Y2 Gc_0 Gc_0))
				(and6x3 (and2_incomplete X6 Y3 Gc_0 Gc_0))
				(and6x4 (and2_incomplete X6 Y4 Gc_0 Gc_0))
				(and6x5 (and2_incomplete X6 Y5 Gc_0 Gc_0))
				(and6x6 (and2 X6 Y6 Gc_0 Gc_0))
				(and6x7 (and2_incomplete X6 Y7 Gc_0 Gc_0))
				(and7x0 (and2_incomplete X7 Y0 Gc_0 Gc_0))
				(and7x1 (and2_incomplete X7 Y1 Gc_0 Gc_0))
				(and7x2 (and2_incomplete X7 Y2 Gc_0 Gc_0))
				(and7x3 (and2_incomplete X7 Y3 Gc_0 Gc_0))
				(and7x4 (and2_incomplete X7 Y4 Gc_0 Gc_0))
				(and7x5 (and2_incomplete X7 Y5 Gc_0 Gc_0))
				(and7x6 (and2_incomplete X7 Y6 Gc_0 Gc_0))
				(and7x7 (and2 X7 Y7 Gc_0 Gc_0))
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
				(S2x8 ((_ extract 3 2) (fa and7x1 C1x7 C2x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C2x8 ((_ extract 1 0) (fa and7x1 C1x7 C2x7 Gc_0 Gc_0 Gc_0 Gc_0)))
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
				(S3x8 ((_ extract 3 2) (fa and6x2 S2x8 C3x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C3x8 ((_ extract 1 0) (fa and6x2 S2x8 C3x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S3x9 ((_ extract 3 2) (fa and7x2 C2x8 C3x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C3x9 ((_ extract 1 0) (fa and7x2 C2x8 C3x8 Gc_0 Gc_0 Gc_0 Gc_0)))
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
				(S4x8 ((_ extract 3 2) (fa and5x3 S3x8 C4x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x8 ((_ extract 1 0) (fa and5x3 S3x8 C4x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S4x9 ((_ extract 3 2) (fa and6x3 S3x9 C4x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x9 ((_ extract 1 0) (fa and6x3 S3x9 C4x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S4x10 ((_ extract 3 2) (fa and7x3 C3x9 C4x9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C4x10 ((_ extract 1 0) (fa and7x3 C3x9 C4x9 Gc_0 Gc_0 Gc_0 Gc_0)))
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
				(S5x8 ((_ extract 3 2) (fa and4x4 S4x8 C5x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x8 ((_ extract 1 0) (fa and4x4 S4x8 C5x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x9 ((_ extract 3 2) (fa and5x4 S4x9 C5x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x9 ((_ extract 1 0) (fa and5x4 S4x9 C5x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x10 ((_ extract 3 2) (fa and6x4 S4x10 C5x9 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x10 ((_ extract 1 0) (fa and6x4 S4x10 C5x9 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S5x11 ((_ extract 3 2) (fa and7x4 C4x10 C5x10 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C5x11 ((_ extract 1 0) (fa and7x4 C4x10 C5x10 Gc_0 Gc_0 Gc_0 Gc_0)))
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
				(S6x8 ((_ extract 3 2) (fa and3x5 S5x8 C6x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x8 ((_ extract 1 0) (fa and3x5 S5x8 C6x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S6x9 ((_ extract 3 2) (fa and4x5 S5x9 C6x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x9 ((_ extract 1 0) (fa and4x5 S5x9 C6x8 Gc_0 Gc_0 Gc_0 Gc_0)))
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
				(S6x12 ((_ extract 3 2) (fa and7x5 C5x11 C6x11 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C6x12 ((_ extract 1 0) (fa and7x5 C5x11 C6x11 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x7 ((_ extract 3 2) (ha and0x7 S6x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x7 ((_ extract 1 0) (ha and0x7 S6x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x8 ((_ extract 3 2) (fa and2x6 S6x8 C7x7 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x8 ((_ extract 1 0) (fa and2x6 S6x8 C7x7 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S7x9 ((_ extract 3 2) (fa and3x6 S6x9 C7x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x9 ((_ extract 1 0) (fa and3x6 S6x9 C7x8 Gc_0 Gc_0 Gc_0 Gc_0)))
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
				(S7x13 ((_ extract 3 2) (fa and7x6 C6x12 C7x12 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C7x13 ((_ extract 1 0) (fa and7x6 C6x12 C7x12 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S8x8 ((_ extract 3 2) (ha and1x7 S7x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x8 ((_ extract 1 0) (ha and1x7 S7x8 Gc_0 Gc_0 Gc_0 Gc_0)))
			)
		(let
			(
				(S8x9 ((_ extract 3 2) (fa and2x7 S7x9 C8x8 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x9 ((_ extract 1 0) (fa and2x7 S7x9 C8x8 Gc_0 Gc_0 Gc_0 Gc_0)))
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
				(S8x14 ((_ extract 3 2) (fa and7x7 C7x13 C8x13 Gc_0 Gc_0 Gc_0 Gc_0)))
				(C8x14 ((_ extract 1 0) (fa and7x7 C7x13 C8x13 Gc_0 Gc_0 Gc_0 Gc_0)))
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
				(Z9_1 ((_ extract 1 1) S8x9))
				(Z10_1 ((_ extract 1 1) S8x10))
				(Z11_1 ((_ extract 1 1) S8x11))
				(Z12_1 ((_ extract 1 1) S8x12))
				(Z13_1 ((_ extract 1 1) S8x13))
				(Z14_1 ((_ extract 1 1) S8x14))
				(Z15_1 ((_ extract 1 1) C8x14))
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
			)
        (let
            (
                (ACCncl (concat ACCo15_1 ACCo14_1 ACCo13_1 ACCo12_1 ACCo11_1 ACCo10_1 ACCo9_1 ACCo8_1 ACCo7_1 ACCo6_1 ACCo5_1 ACCo4_1 ACCo3_1 ACCo2_1 ACCo1_1 ACCo0_1))
            )
        (let
			(
                (Psync (bvmul (concat (_ bv0 8) (rail1 X7) (rail1 X6) (rail1 X5) (rail1 X4) (rail1 X3) (rail1 X2) (rail1 X1) (rail1 X0)) (concat (_ bv0 8) (rail1 Y7) (rail1 Y6) (rail1 Y5) (rail1 Y4) (rail1 Y3) (rail1 Y2) (rail1 Y1) (rail1 Y0))))
            )
        (let
            (
                (ACCsync (bvadd Psync (concat (rail1 ACC15) (rail1 ACC14) (rail1 ACC13) (rail1 ACC12) (rail1 ACC11) (rail1 ACC10) (rail1 ACC9) (rail1 ACC8) (rail1 ACC7) (rail1 ACC6) (rail1 ACC5) (rail1 ACC4) (rail1 ACC3) (rail1 ACC2) (rail1 ACC1) (rail1 ACC0))))
            )
        (=>
            (and
                (= (_ bv0 1) Gc_0)
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
				(datap ACC0)
				(datap ACC1)
				(datap ACC2)
				(datap ACC3)
				(datap ACC4)
				(datap ACC5)
				(datap ACC6)
				(datap ACC7)
				(datap ACC8)
				(datap ACC9)
				(datap ACC10)
				(datap ACC11)
				(datap ACC12)
				(datap ACC13)
				(datap ACC14)
				(datap ACC15)
            )
			(= ACCsync ACCncl)
        )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    )
)

(check-sat)
(get-model)
