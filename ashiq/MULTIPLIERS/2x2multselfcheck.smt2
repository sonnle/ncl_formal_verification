; Formal verification proof - input completeness of test_netlist2x2.txt
(set-logic QF_BV)

; Inputs: a0, a1, b0, b1
(declare-fun a0 () (_ BitVec 1))
(declare-fun a1 () (_ BitVec 1))
(declare-fun b0 () (_ BitVec 1))
(declare-fun b1 () (_ BitVec 1))

; Outputs: p0, p1, p2, p3
(declare-fun p0 () (_ BitVec 1))
(declare-fun p1 () (_ BitVec 1))
(declare-fun p2 () (_ BitVec 1))
(declare-fun p3 () (_ BitVec 1))

; SAT/UNSAT assertion for test_netlist2x2.txt
(assert
	(not		
		(let
			(
				(p0 (bvand a0 b0))
				(t0 (bvand a1 b0))
				(t1 (bvand a0 b1))
				(t3 (bvand a1 b1))
			)		
		(let
			(
				(p1 (bvxor t0 t1))
				(t2 (bvand t0 t1))
			)		
		(let
			(
				(p2 (bvxor t2 t3))
				(p3 (bvand t2 t3))
			)
		(let
			(
				(x_t (concat (_ bv0 2) a1 a0))
				(y_t (concat (_ bv0 2) b1 b0))
			)
		(let 
			(
				(out_pchb (concat p3 p2 p1 p0))
				(out_sync (bvmul x_t y_t))
				
			)
			
		(= out_pchb out_sync) )))))
	)	
)
(check-sat)
(get-model)

(get-value (a1))
(get-value (a0))
(get-value (b1))
(get-value (b0))
(get-value (p0))
(get-value (p1))
(get-value (p2))
(get-value (p3))