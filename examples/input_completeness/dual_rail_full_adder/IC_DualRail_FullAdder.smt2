; Formal verification proof of input completeness of NCL 2-bit Full Adder
(set-logic QF_BV)

; Inputs
(declare-fun X     () (_ BitVec 2))
(declare-fun Y     () (_ BitVec 2))
(declare-fun Cin   () (_ BitVec 2))

; Outputs
(declare-fun S_t     () (_ BitVec 2))
(declare-fun Cout_t  () (_ BitVec 2))

; Extract rail0 of a dual rail signal
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 0 0) a)
)

; Extract rail1 of a dual rail signal
(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 1 1) a)
)

; Determine if the dual rail signal is null (0x00)
(define-fun nullp ((a (_ BitVec 2))) (Bool)
    (and
        (= (_ bv0 1) (rail0 a))
        (= (_ bv0 1) (rail1 a)))
)

; Determine if the dual rail signal is valid (not 0x11)
(define-fun legalp ((a (_ BitVec 2))) (Bool)
    (not
        (and
            (= (_ bv1 1) (rail0 a))
            (= (_ bv1 1) (rail1 a))))
)

(define-fun X0 () (_ BitVec 1) (rail0 X))
(define-fun Y0 () (_ BitVec 1) (rail0 Y))
(define-fun Cin0 () (_ BitVec 1) (rail0 Cin))

(define-fun X1 () (_ BitVec 1) (rail1 X))
(define-fun Y1 () (_ BitVec 1) (rail1 Y))
(define-fun Cin1 () (_ BitVec 1) (rail1 Cin))

(define-fun Th23 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
                    (bvand b c)
                    (bvand a c)))
            (_ bv1 1)
            g_l))
)

(define-fun Th34w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
            g_l))
)

(declare-fun Gc_0 () (_ BitVec 1))
(declare-fun Gc_1 () (_ BitVec 1))
(declare-fun Gc_2 () (_ BitVec 1))
(declare-fun Gc_3 () (_ BitVec 1))

(assert
    (not
        (let
            (
                (Gn_0 (Th23 Cin0 X0 Y0 Gc_0))
                (Gn_1 (Th23 Cin1 X1 Y1 Gc_1))
                (Gn_2 (Th34w2 Gc_1 Cin0 X0 Y0 Gc_2))
                (Gn_3 (Th34w2 Gc_0 Cin1 X1 Y1 Gc_3))
            )
            (let
                (
                	(Cout (concat Gn_1 Gn_0))
                	(S    (concat Gn_3 Gn_2))
                )
			(=>
				(and
;                    (= S S_t)
;                    (= Cout Cout_t)
					(not (= (_ bv3 2) X))
					(not (= (_ bv3 2) Y))
					(not (= (_ bv3 2) Cin))
					(= (_ bv0 1) Gc_0)
					(= (_ bv0 1) Gc_1)
					(= (_ bv0 1) Gc_2)
					(= (_ bv0 1) Gc_3)
					(or
						(nullp X)
						(nullp Y)
						(nullp Cin)))
				(or (nullp S)
					(nullp Cout))))))
)

(check-sat)
(get-model)
