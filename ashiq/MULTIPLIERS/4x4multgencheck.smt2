; Formal verification proof - input completeness of test_netlist4x4.txt
(set-logic QF_BV)

; Inputs: x0, x1, x2, x3, y0, y1, y2, y3
(declare-fun x0 () (_ BitVec 1))
(declare-fun x1 () (_ BitVec 1))
(declare-fun x2 () (_ BitVec 1))
(declare-fun x3 () (_ BitVec 1))
(declare-fun y0 () (_ BitVec 1))
(declare-fun y1 () (_ BitVec 1))
(declare-fun y2 () (_ BitVec 1))
(declare-fun y3 () (_ BitVec 1))

; Outputs: p0, p1, p2, p3, p4, p5, p6, p7
(declare-fun p0 () (_ BitVec 1))
(declare-fun p1 () (_ BitVec 1))
(declare-fun p2 () (_ BitVec 1))
(declare-fun p3 () (_ BitVec 1))
(declare-fun p4 () (_ BitVec 1))
(declare-fun p5 () (_ BitVec 1))
(declare-fun p6 () (_ BitVec 1))
(declare-fun p7 () (_ BitVec 1))

; SAT/UNSAT assertion for test_netlist4x4.txt
(assert
	(not		
		(let
			(
				(p0 (bvand x0 y0))
				(t0 (bvand x1 y0))
				(t1 (bvand x0 y1))
				(t2 (bvand x2 y0))
				(t3 (bvand x1 y1))
				(t7 (bvand x3 y0))
				(t8 (bvand x2 y1))
				(m2 (bvand x3 y1))
				(m3 (bvand x0 y2))
				(m4 (bvand x1 y2))
				(m8 (bvand x2 y2))
				(n2 (bvand x3 y2))
				(n6 (bvand x0 y3))
				(n7 (bvand x1 y3))
				(q1 (bvand x2 y3))
				(q5 (bvand x3 y3))
			)		
		(let
			(
				(p1 (bvxor t0 t1))
				(c0 (bvand t0 t1))
				(t4 (bvxor t2 t3))
				(t6 (bvand t2 t3))
				(t9 (bvxor t7 t8))
				(m0 (bvand t7 t8))
			)		
		(let
			(
				(s1 (bvxor c0 t4))
				(t5 (bvand c0 t4))
			)		
		(let
			(
				(c1 (bvor t6 t5))
				(p2 (bvxor s1 m3))
				(c4 (bvand s1 m3))
			)		
		(let
			(
				(s2 (bvxor c1 t9))
				(m1 (bvand c1 t9))
			)		
		(let
			(
				(c2 (bvor m0 m1))
				(m5 (bvxor m4 s2))
				(m6 (bvand m4 s2))
			)		
		(let
			(
				(s3 (bvxor c2 m2))
				(c3 (bvand c2 m2))
				(s4 (bvxor c4 m5))
				(m7 (bvand c4 m5))
			)		
		(let
			(
				(c5 (bvor m7 m6))
				(m9 (bvxor s3 m8))
				(n0 (bvand s3 m8))
				(n3 (bvxor c3 n2))
				(n4 (bvand c3 n2))
				(p3 (bvxor s4 n6))
				(c8 (bvand s4 n6))
			)		
		(let
			(
				(s5 (bvxor m9 c5))
				(n1 (bvand m9 c5))
			)		
		(let
			(
				(c6 (bvor n0 n1))
				(n8 (bvxor s5 n7))
				(n9 (bvand s5 n7))
			)		
		(let
			(
				(s6 (bvxor c6 n3))
				(n5 (bvand c6 n3))
				(p4 (bvxor c8 n8))
				(q0 (bvand c8 n8))
			)		
		(let
			(
				(c7 (bvor n5 n4))
				(c9 (bvor q0 n9))
				(q2 (bvxor s6 q1))
				(q3 (bvand s6 q1))
			)		
		(let
			(
				(p5 (bvxor c9 q2))
				(q4 (bvand c9 q2))
				(q6 (bvxor q5 c7))
				(q7 (bvand q5 c7))
			)		
		(let
			(
				(d0 (bvor q3 q4))
			)		
		(let
			(
				(p6 (bvxor q6 d0))
				(q8 (bvand d0 q6))
			)		
		(let
			(
				(p7 (bvor q8 q7))
			)
		
		
		
		(let
			(
				(x_t (concat (_ bv0 4) x3 x2 x1 x0))
				(y_t (concat (_ bv0 4) y3 y2 y1 y0))
			)
		(let 
			(
				(out_pchb (concat p7 p6 p5 p4 p3 p2 p1 p0))
				(out_sync (bvmul x_t y_t))
				
			)
			
		(= out_pchb out_sync)))))))))))))))))))
	)	
)
(check-sat)
(get-model)
