(set-logic QF_BV)

(declare-fun X0 () (_ BitVec 2))
(declare-fun X1 () (_ BitVec 2))
(declare-fun X2 () (_ BitVec 2))
(declare-fun X3 () (_ BitVec 2))

(declare-fun Y0 () (_ BitVec 2))
(declare-fun Y1 () (_ BitVec 2))
(declare-fun Y2 () (_ BitVec 2))
(declare-fun Y3 () (_ BitVec 2))

(declare-fun ACC0 () (_ BitVec 2))
(declare-fun ACC1 () (_ BitVec 2))
(declare-fun ACC2 () (_ BitVec 2))
(declare-fun ACC3 () (_ BitVec 2))
(declare-fun ACC4 () (_ BitVec 2))
(declare-fun ACC5 () (_ BitVec 2))
(declare-fun ACC6 () (_ BitVec 2))
(declare-fun ACC7 () (_ BitVec 2))

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
                (and1x0 (and2_incomplete X1 Y0 Gc_0 Gc_0))
                (and1x1 (and2 X1 Y1 Gc_0 Gc_0))
                (and1x2 (and2_incomplete X1 Y2 Gc_0 Gc_0))
                (and1x3 (and2_incomplete X1 Y3 Gc_0 Gc_0))
                (and2x0 (and2_incomplete X2 Y0 Gc_0 Gc_0))
                (and2x1 (and2_incomplete X2 Y1 Gc_0 Gc_0))
                (and2x2 (and2 X2 Y2 Gc_0 Gc_0))
                (and2x3 (and2_incomplete X2 Y3 Gc_0 Gc_0))
                (and3x0 (and2_incomplete X3 Y0 Gc_0 Gc_0))
                (and3x1 (and2_incomplete X3 Y1 Gc_0 Gc_0))
                (and3x2 (and2_incomplete X3 Y2 Gc_0 Gc_0))
                (and3x3 (and2 X3 Y3 Gc_0 Gc_0))
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
                (S2x4 ((_ extract 3 2) (fa and3x1 C1x3 C2x3 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C2x4 ((_ extract 1 0) (fa and3x1 C1x3 C2x3 Gc_0 Gc_0 Gc_0 Gc_0)))
            )
        (let
            (
                (S3x3 ((_ extract 3 2) (ha and0x3 S2x3 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C3x3 ((_ extract 1 0) (ha and0x3 S2x3 Gc_0 Gc_0 Gc_0 Gc_0)))
            )
        (let
            (
                (S3x4 ((_ extract 3 2) (fa and2x2 S2x4 C3x3 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C3x4 ((_ extract 1 0) (fa and2x2 S2x4 C3x3 Gc_0 Gc_0 Gc_0 Gc_0)))
            )
        (let
            (
                (S3x5 ((_ extract 3 2) (fa and3x2 C2x4 C3x4 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C3x5 ((_ extract 1 0) (fa and3x2 C2x4 C3x4 Gc_0 Gc_0 Gc_0 Gc_0)))
            )
        (let
            (
                (S4x4 ((_ extract 3 2) (ha and1x3 S3x4 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C4x4 ((_ extract 1 0) (ha and1x3 S3x4 Gc_0 Gc_0 Gc_0 Gc_0)))
            )
        (let
            (
                (S4x5 ((_ extract 3 2) (fa and2x3 S3x5 C4x4 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C4x5 ((_ extract 1 0) (fa and2x3 S3x5 C4x4 Gc_0 Gc_0 Gc_0 Gc_0)))
            )
        (let
            (
                (S4x6 ((_ extract 3 2) (fa and3x3 C3x5 C4x5 Gc_0 Gc_0 Gc_0 Gc_0)))
                (C4x6 ((_ extract 1 0) (fa and3x3 C3x5 C4x5 Gc_0 Gc_0 Gc_0 Gc_0)))
            )
        (let
            (
                (Z0 S0x0)
                (Z1 S1x1)
                (Z2 S2x2)
                (Z3 S3x3)
                (Z4 S4x4)
                (Z5 S4x5)
                (Z6 S4x6)
                (Z7 C4x6)
            )
        (let
            (
                (Pncl (concat (rail1 Z7) (rail1 Z6) (rail1 Z5) (rail1 Z4) (rail1 Z3) (rail1 Z2) (rail1 Z1) (rail1 Z0)))
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
			)
        (let
			(
				(ACCo0 (concat (rail1 P0) (bvnot (rail1 P0))))
                (ACCo1 (concat (rail1 P1) (bvnot (rail1 P1))))
                (ACCo2 (concat (rail1 P2) (bvnot (rail1 P2))))
                (ACCo3 (concat (rail1 P3) (bvnot (rail1 P3))))
                (ACCo4 (concat (rail1 P4) (bvnot (rail1 P4))))
                (ACCo5 (concat (rail1 P5) (bvnot (rail1 P5))))
                (ACCo6 (concat (rail1 P6) (bvnot (rail1 P6))))
                (ACCo7 (concat (rail1 P7) (bvnot (rail1 P7))))
			)
        (let
            (
                (ACCncl (concat (rail1 ACCo7) (rail1 ACCo6) (rail1 ACCo5) (rail1 ACCo4) (rail1 ACCo3) (rail1 ACCo2) (rail1 ACCo1) (rail1 ACCo0)))
            )
        (let
			(
                (Psync (bvmul (concat (_ bv0 4) (rail1 Xi3) (rail1 Xi2) (rail1 Xi1) (rail1 Xi0)) (concat (_ bv0 4) (rail1 Yi3) (rail1 Yi2) (rail1 Yi1) (rail1 Yi0))))
            )
        (let
            (
                (ACCsync (bvadd Psync (concat (rail1 ACCi7) (rail1 ACCi6) (rail1 ACCi5) (rail1 ACCi4) (rail1 ACCi3) (rail1 ACCi2) (rail1 ACCi1) (rail1 ACCi0))))
            )
        (=>
            (and
                (= (_ bv0 1) Gc_0)
                (datap Xi0)
				(datap Xi1)
				(datap Xi2)
				(datap Xi3)
				(datap Yi0)
				(datap Yi1)
				(datap Yi2)
				(datap Yi3)
				(datap ACCi0)
				(datap ACCi1)
				(datap ACCi2)
				(datap ACCi3)
				(datap ACCi4)
				(datap ACCi5)
				(datap ACCi6)
				(datap ACCi7)
            )
            (= ACCsync ACCncl)
        )))))))))))))))))))))))))))))
    )
)

(check-sat)
(get-model)
