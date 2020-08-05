;formal verification of module1 design
(set-logic QF_BV)

;inputs: x, j, k, n0 to n3, e0 to e3, d0 to d3, gc for threshold gate
(declare-fun x () (_ BitVec 2))

(declare-fun j0 () (_ BitVec 2))
(declare-fun k0 () (_ BitVec 2))
(declare-fun j1 () (_ BitVec 2))
(declare-fun k1 () (_ BitVec 2))

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
(declare-fun mulout() (_ BitVec 8))

;NCL gate Boolean function - TH12: (A + B)
(define-fun th12 ((a (_ BitVec 1)) (b (_ BitVec 1)) (g1 (_ BitVec 1))) (_ BitVec 1)
	(bvor a b)
)

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

;NCL gate Boolean function - THand0: (AB + BC + AD)
(define-fun thand0 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
	(bvor (bvor (bvand a b) (bvand b c)) (bvand a d))
)

;NCL gate Boolean function - TH24comp: (AC + BC + AD + BD)
(define-fun th24comp ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
	(bvor (bvor (bvand a c) (bvand b c)) (bvor (bvand a d) (bvand b d)))
)

;NCL gate Boolean function - TH23: (AB + AC + BC)
(define-fun th23 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
	(bvor (bvand a b) (bvor (bvand b c) (bvand a c)))
)

;NCL gate Boolean function - TH34w2: (AB + AC + AD + BCD)
(define-fun th34w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
	(bvor (bvor (bvand a b) (bvand a c)) (bvor (bvand a d) (bvand b (bvand c d))))
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

(define-fun nullp ((a (_ BitVec 2))) (Bool)
    (= (_ bv0 2) a)
)

(define-fun illegalp ((a (_ BitVec 2))) (Bool)
    (= (_ bv3 2) a)
)

;ncl half adder sum
(define-fun ha_sum ((x (_ BitVec 2)) (y (_ BitVec 2)) (gl (_ BitVec 1))) (_ BitVec 2)
	(let
		(
			(S0 (th24comp (rail0 y) (rail1 x) (rail0 x) (rail1 y) gl))
			(S1 (th24comp (rail0 y) (rail0 x) (rail1 y) (rail1 x) gl))
		)
	(let
		(
			(S (concat S1 S0))
		)
	))
)

;ncl half adder carry
(define-fun ha_carry ((x (_ BitVec 2)) (y (_ BitVec 2)) (gl (_ BitVec 1))) (_ BitVec 2)
	(let
		(
			(C0 (th12 (rail0 x) (rail0 y) gl))
			(C1 (th22 (rail1 x) (rail1 y) gl))
		)
	(let
		(
			(C (concat C1 C0))
		)
	))
)

;ncl full adder sum
(define-fun fa_sum ((x (_ BitVec 2)) (y (_ BitVec 2)) (c (_ BitVec 2)) (gl (_ BitVec 1))) (_ BitVec 2)
	(let
		(
			(I0 (th23 (rail0 c) (rail0 x) (rail0 y) gl))
			(I1 (th23 (rail1 c) (rail1 x) (rail1 y) gl))
		)
	(let
		(
			(S0 (th34w2 I1 (rail0 c) (rail0 x) (rail0 y) gl))
			(S1 (th34w2 I0 (rail1 c) (rail1 x) (rail1 y) gl))
		)
	(let
		(
			(S (concat S1 S0))
		)
	)))
)

;ncl full adder carry
(define-fun fa_carry ((x (_ BitVec 2)) (y (_ BitVec 2)) (c (_ BitVec 2)) (gl (_ BitVec 1))) (_ BitVec 2)
	(let
		(
			(Cout0 (th23 (rail0 c) (rail0 x) (rail0 y) gl))
			(Cout1 (th23 (rail1 c) (rail1 x) (rail1 y) gl))
		)
	(let
		(
			(Cout (concat Cout1 Cout0))
		)
	))
)

;ncl input complete AND gate
(define-fun ncl_and ((x (_ BitVec 2)) (y (_ BitVec 2)) (gl (_ BitVec 1))) (_ BitVec 2)
	(let
		(
			(Z0 (thand0 (rail0 y) (rail0 x) (rail1 y) (rail1 x) gl))
			(Z1 (th22 (rail1 x) (rail1 y) gl))
		)
	(let
		(
			(Z (concat Z1 Z0))
		)
	))
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

;ncl 2x2 multiplier
(define-fun multiplier ((a (_ BitVec 4)) (b (_ BitVec 4)) (gl (_ BitVec 1))) (_ BitVec 8)
	(let
		(
			(J1 ((_ extract 3 2) a))
			(J0 ((_ extract 1 0) a))
			(K1 ((_ extract 3 2) b))
			(K0 ((_ extract 1 0) b))
		)
	(let
		(
			(M0 (ncl_and J0 K0 gl)) ;J0K0
			(J0K1 (ncl_and J0 K1 gl))
			(J1K0 (ncl_and J1 K0 gl))
			(J1K1 (ncl_and J1 K1 gl))
		)
	(let
		(
			(M1 (ha_sum J0K1 J1K0 gl))
			(C1 (ha_carry J0K1 J1K0 gl))
		)
	(let
		(
			(M2 (ha_sum J1K1 C1 gl))
			(M3 (ha_carry J1K1 C1 gl))
		)
	(let
		(
			(M (concat M3 M2 M1 M0))
		)
	)))))
)

;single bit to dual rail
(define-fun to_DR ((a (_ BitVec 1))) (_ BitVec 2)
	(ite (= a (_ bv0 1)) (_ bv1 2) (_ bv2 2))
)

;boolean multiplier
(define-fun boolmultiplier ((a (_ BitVec 2)) (b (_ BitVec 2))) (_ BitVec 4)
	(let
		(
			(aout (concat (_ bv0 2) a))
			(bout (concat (_ bv0 2) b))
		)
	(let
		(
			(out (bvmul aout bout))
		)
	))
)		

;SAT/UNSAT assertion
(assert
	(not
		(let
			(
				(boolmuxsel (bvand (rail1 j0) (rail0 j0)))
				(nreg (concat n3 n2 n1 n0))
				(ereg (concat e3 e2 e1 e0))
				(dreg (concat d3 d2 d1 d0))
				(T1 (concat j1 j0))
				(T2 (concat k1 k0))
				(j0rail1 (rail1 j0))
				(j1rail1 (rail1 j1))
				(k0rail1 (rail1 k0))
				(k1rail1 (rail1 k1))
			)
		(let
			(
				(boolmuxout (boolmux ereg dreg boolmuxsel))
				(mulout (multiplier T1 T2 gc))
				(J (concat j1rail1 j0rail1))
				(K (concat k1rail1 k0rail1))
			)
		(let
			(
				(z (nclmux nreg boolmuxout x gc))
				(bvmulout (boolmultiplier J K))
			)
		(let
			(
				(b3 ((_ extract 3 3) bvmulout))
				(b2 ((_ extract 2 2) bvmulout))
				(b1 ((_ extract 1 1) bvmulout))
				(b0 ((_ extract 0 0) bvmulout))
			)
		(let
			(
				(bdr3 (to_DR b3))
				(bdr2 (to_DR b2))
				(bdr1 (to_DR b1))
				(bdr0 (to_DR b0))
			)
		(let
			(
				(bfinal (concat bdr3 bdr2 bdr1 bdr0))
			)
		
				(= boolmuxsel (_ bv0 1))
		))))))
	)
)

(check-sat)
(get-model)
