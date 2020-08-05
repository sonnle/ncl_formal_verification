(set-logic QF_BV)

; Inputs: X, B, K
(declare-fun X () (_ BitVec 2))
(declare-fun B () (_ BitVec 2))
(declare-fun K () (_ BitVec 2))
(declare-fun Gc_0 () (_ BitVec 1))

; Outputs: Z
(declare-fun Z () (_ BitVec 2))

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
				(F0 (mux I0 I2 (rail0 X)))
				(F1 (mux I1 I3 (rail0 X)))
			)
		(let
			(
				(Z (concat F1 F0))
			)
		(=>
			(and
				(datap X)
				(datap B)
				(datap K)
				(= I0 (_ bv1 1))
				(= Gc_0 (_ bv0 1))
			)
			(not
				(datap Z))))))
	)
)

(check-sat)
(get-model)
