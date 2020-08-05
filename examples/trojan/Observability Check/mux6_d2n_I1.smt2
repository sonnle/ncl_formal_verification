(set-logic QF_BV)

; Inputs: X, B, K
(declare-fun X () (_ BitVec 2))
(declare-fun B () (_ BitVec 2))
(declare-fun K () (_ BitVec 2))
(declare-fun X_d () (_ BitVec 2))
(declare-fun B_d () (_ BitVec 2))
(declare-fun K_d () (_ BitVec 2))
(declare-fun Gc_0 () (_ BitVec 1))

; Outputs: Z
(declare-fun Z () (_ BitVec 2))
(declare-fun Z_d () (_ BitVec 2))

; Extract rail0 of a dual rail signal
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 0 0) a)
)

; Extract rail1 of a dual rail signal
(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 1 1) a)
)

(define-fun datap ((a (_ BitVec 2))) (Bool)
    (or
        (= (_ bv1 2) a)
        (= (_ bv2 2) a)
    )
)

(define-fun nullp ((a (_ BitVec 2))) (Bool)
    (= (_ bv0 2) a)
)

; NCL Gate Boolean Function - TH22: (AB)
(define-fun th22 ((a (_ BitVec 1)) (b (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
    (ite
        (=  (_ bv1 1) (bvand (bvnot a) (bvnot b)))
        (_ bv0 1)
        (ite
            (=  (_ bv1 1) (bvand a b)) (_ bv1 1) 
			gl))
)

; mux function
(define-fun mux ((a (_ BitVec 1)) (b (_ BitVec 1)) (sel (_ BitVec 1))) (_ BitVec 1)
	(ite (= sel (_ bv0 1)) a b)
)

; Current values of threshold gates

(assert
	(not
		(let
			(
				(I0 (mux (rail0 B) (rail0 K) (rail0 X)))
				(I1 (mux (rail1 B) (rail1 K) (rail0 X)))
				(I2 (mux (rail0 B) (rail0 K) (rail1 X)))
				(I3 (mux (rail1 B) (rail1 K) (rail1 X)))
			)
		(let
			(
				(I0_d (mux (rail0 B_d) (rail0 K_d) (rail0 X_d)))
				(I1_d (mux (rail1 B_d) (rail1 K_d) (rail0 X_d)))
				(I2_d (mux (rail0 B_d) (rail0 K_d) (rail1 X_d)))
				(I3_d (mux (rail1 B_d) (rail1 K_d) (rail1 X_d)))
			)
		(let
			(
				(F0 (mux I0 I2 (rail0 X)))
				(F1 (mux I1 I3 (rail0 X)))
			)
		(let
			(
				(F0_d (mux I0_d I2_d (rail0 X_d)))
				(F1_d (mux I1_d I3_d (rail0 X_d)))
			)
		(let
			(
				(Z (concat F1 F0))
				(Z_d (concat F1_d F0_d))
			)
		(=>
			(and
				(datap X)
				(datap B)
				(datap K)
				(nullp X_d)
				(nullp B_d)
				(nullp K_d)
				(= I1 (_ bv1 1))
				(= Gc_0 (_ bv0 1))
			)
			(not
				(nullp Z_d))))))))
	)
)

(check-sat)
(get-model)
