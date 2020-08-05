;formal verification of module1 design
(set-logic QF_BV)

;inputs: x, y, n0 to n3, e0 to e3, d0 to d3, gc for threshold gate
(declare-fun x () (_ BitVec 2))
(declare-fun y () (_ BitVec 2))

(declare-fun n0 () (_ BitVec 2))
(declare-fun n1 () (_ BitVec 2))
(declare-fun n2 () (_ BitVec 2))
(declare-fun n3 () (_ BitVec 2))

(declare-fun e0 () (_ BitVec 2))
(declare-fun e1 () (_ BitVec 2))
(declare-fun e2 () (_ BitVec 2))
(declare-fun e3 () (_ BitVec 2))

(declare-fun d0 () (_ BitVec 2))
(declare-fun d1 () (_ BitVec 2))
(declare-fun d2 () (_ BitVec 2))
(declare-fun d3 () (_ BitVec 2))

(declare-fun gc () (_ BitVec 1))

;outputs: z
(declare-fun z () (_ BitVec 8))


;NCL gate Boolean function - TH33: (ABC)
(define-fun th33 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
	(bvand a (bvand b c))
)
	
;NCL gate Boolean function - TH14: (A + B + C + D)
(define-fun th14 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (g1 (_ BitVec 1))) (_ BitVec 1)
	(bvor a (bvor b (bvor c d)))
)
	
;NCL gate Boolean function - TH22: (AB)
(define-fun th22 ((a (_ BitVec 1)) (b (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
	(bvand a b)
)
	
;extract rail0
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
	((_ extract 0 0) a)
)
	
;extract rail1
(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
	((_ extract 1 1) a)
)
	
;determine if dual rail is valid data
(define-fun datap ((a (_ BitVec 2))) (Bool)
	(or
		(= (_ bv1 2) a)
		(= (_ bv2 2) a)
	)
)

;determine if dual rail is illegal
(define-fun illegalp ((a (_ BitVec 2))) (Bool)
	(and
		(= (_ bv1 1) (rail0 a))
		(= (_ bv1 1) (rail1 a))
	)
)
	
;boolean mux
(define-fun boolmux ((a (_ BitVec 8)) (b (_ BitVec 8)) (s (_ BitVec 1))) (_ BitVec 8)
	(ite (= s (_ bv0 1)) a b)
)

;input complete ncl mux
(define-fun nclmux ((a (_ BitVec 8)) (b (_ BitVec 8)) (s (_ BitVec 2)) (gl (_ BitVec 1))) (_ BitVec 8)
	(let
		(
			(X3 ((_ extract 7 6) a))
			(X2 ((_ extract 5 4) a))
			(X1 ((_ extract 3 2) a))
			(X0 ((_ extract 1 0) a))
			(Y3 ((_ extract 7 6) b))
			(Y2 ((_ extract 5 4) b))
			(Y1 ((_ extract 3 2) b))
			(Y0 ((_ extract 1 0) b))
		)
	(let
		(
			(I0 (th33 (rail0 X0) (rail0 Y0) (rail0 s) gl))
			(I1 (th33 (rail0 X0) (rail0 Y0) (rail1 s) gl))
			(I2 (th33 (rail0 X0) (rail1 Y0) (rail0 s) gl))
			(I3 (th33 (rail1 X0) (rail0 Y0) (rail1 s) gl))
			(I4 (th33 (rail0 X0) (rail1 Y0) (rail1 s) gl))
			(I5 (th33 (rail1 X0) (rail1 Y0) (rail0 s) gl))
			(I6 (th33 (rail1 X0) (rail1 Y0) (rail1 s) gl))
			(I7 (th33 (rail1 X0) (rail0 Y0) (rail0 s) gl))
			
			(I10 (th33 (rail0 X1) (rail0 Y1) (rail0 s) gl))
			(I11 (th33 (rail0 X1) (rail0 Y1) (rail1 s) gl))
			(I12 (th33 (rail0 X1) (rail1 Y1) (rail0 s) gl))
			(I13 (th33 (rail1 X1) (rail0 Y1) (rail1 s) gl))
			(I14 (th33 (rail0 X1) (rail1 Y1) (rail1 s) gl))
			(I15 (th33 (rail1 X1) (rail1 Y1) (rail0 s) gl))
			(I16 (th33 (rail1 X1) (rail1 Y1) (rail1 s) gl))
			(I17 (th33 (rail1 X1) (rail0 Y1) (rail0 s) gl))
			
			(I20 (th33 (rail0 X2) (rail0 Y2) (rail0 s) gl))
			(I21 (th33 (rail0 X2) (rail0 Y2) (rail1 s) gl))
			(I22 (th33 (rail0 X2) (rail1 Y2) (rail0 s) gl))
			(I23 (th33 (rail1 X2) (rail0 Y2) (rail1 s) gl))
			(I24 (th33 (rail0 X2) (rail1 Y2) (rail1 s) gl))
			(I25 (th33 (rail1 X2) (rail1 Y2) (rail0 s) gl))
			(I26 (th33 (rail1 X2) (rail1 Y2) (rail1 s) gl))
			(I27 (th33 (rail1 X2) (rail0 Y2) (rail0 s) gl))
			
			(I30 (th33 (rail0 X3) (rail0 Y3) (rail0 s) gl))
			(I31 (th33 (rail0 X3) (rail0 Y3) (rail1 s) gl))
			(I32 (th33 (rail0 X3) (rail1 Y3) (rail0 s) gl))
			(I33 (th33 (rail1 X3) (rail0 Y3) (rail1 s) gl))
			(I34 (th33 (rail0 X3) (rail1 Y3) (rail1 s) gl))
			(I35 (th33 (rail1 X3) (rail1 Y3) (rail0 s) gl))
			(I36 (th33 (rail1 X3) (rail1 Y3) (rail1 s) gl))
			(I37 (th33 (rail1 X3) (rail0 Y3) (rail0 s) gl))
		)
	(let
		(
			(F0_0 (th14 I0 I1 I2 I3 gl))
			(F0_1 (th14 I4 I5 I6 I7 gl))
			
			(F1_0 (th14 I10 I11 I12 I13 gl))
			(F1_1 (th14 I14 I15 I16 I17 gl))
			
			(F2_0 (th14 I20 I21 I22 I23 gl))
			(F2_1 (th14 I24 I25 I26 I27 gl))
			
			(F3_0 (th14 I30 I31 I32 I33 gl))
			(F3_1 (th14 I34 I35 I36 I37 gl))
		)
		
	(let
		(
			(out (concat F3_1 F3_0 F2_1 F2_0 F1_1 F1_0 F0_1 F0_0))
		)
	)))))		

;SAT/UNSAT assertion
(assert
	(not
		(let
			(
				(boolmuxsel (th22 (rail1 y) (rail0 y) gc))
				(nreg (concat n3 n2 n1 n0))
				(ereg (concat e3 e2 e1 e0))
				(dreg (concat d3 d2 d1 d0))
			)
		(let
			(
				(boolmuxout (boolmux ereg dreg boolmuxsel))
			)
		(let
			(
				(z (nclmux nreg boolmuxout x gc))
			)
		(=>
			(and
				(= (_ bv0 1) gc)
				(datap n3)
				(datap n2)
				(datap n1)
				(datap n0)
				(datap e3)
				(datap e2)
				(datap e1)
				(datap e0)
				(datap d3)
				(datap d2)
				(datap d1)
				(datap d0)
				(datap x)
				(illegalp y)
			)
			(or
				(= z nreg)
				(= z ereg)
				;(= z dreg)
			)
		))))
	)
)

(check-sat)
(get-model)