; Formal verification proof - input completeness of test_netlist5x5.txt
(set-logic QF_BV)

; Inputs: x0, x1, x2, x3, x4, y0, y1, y2, y3, y4
(declare-fun x0 () (_ BitVec 1))
(declare-fun x1 () (_ BitVec 1))
(declare-fun x2 () (_ BitVec 1))
(declare-fun x3 () (_ BitVec 1))
(declare-fun x4 () (_ BitVec 1))
(declare-fun y0 () (_ BitVec 1))
(declare-fun y1 () (_ BitVec 1))
(declare-fun y2 () (_ BitVec 1))
(declare-fun y3 () (_ BitVec 1))
(declare-fun y4 () (_ BitVec 1))

; Outputs: p0, p1, p2, p3, p4, p5, p6, p7, p8, p9
(declare-fun p0 () (_ BitVec 1))
(declare-fun p1 () (_ BitVec 1))
(declare-fun p2 () (_ BitVec 1))
(declare-fun p3 () (_ BitVec 1))
(declare-fun p4 () (_ BitVec 1))
(declare-fun p5 () (_ BitVec 1))
(declare-fun p6 () (_ BitVec 1))
(declare-fun p7 () (_ BitVec 1))
(declare-fun p8 () (_ BitVec 1))
(declare-fun p9 () (_ BitVec 1))

; SAT/UNSAT assertion for test_netlist5x5.txt
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
				(t12 (bvand x4 y0))
				(t13 (bvand x3 y1))
				(t17 (bvand x4 y1))
				(t18 (bvand x0 y2))
				(t19 (bvand x1 y2))
				(t23 (bvand x2 y2))
				(t27 (bvand x3 y2))
				(t31 (bvand x4 y2))
				(t35 (bvand x0 y3))
				(t36 (bvand x1 y3))
				(t40 (bvand x2 y3))
				(t44 (bvand x3 y3))
				(t48 (bvand x4 y3))
				(t52 (bvand x0 y4))
				(t53 (bvand x1 y4))
				(t57 (bvand x2 y4))
				(t61 (bvand x3 y4))
				(t65 (bvand x4 y4))
			)		
		(let
			(
				(p1 (bvxor t0 t1))
				(c0 (bvand t0 t1))
				(t4 (bvxor t2 t3))
				(t6 (bvand t2 t3))
				(t9 (bvxor t7 t8))
				(t10 (bvand t7 t8))
				(t14 (bvxor t12 t13))
				(t15 (bvand t12 t13))
			)		
		(let
			(
				(s1 (bvxor c0 t4))
				(t5 (bvand c0 t4))
			)		
		(let
			(
				(c1 (bvor t6 t5))
				(p2 (bvxor s1 t18))
				(c5 (bvand s1 t18))
			)		
		(let
			(
				(s2 (bvxor c1 t9))
				(t11 (bvand c1 t9))
			)		
		(let
			(
				(c2 (bvor t10 t11))
				(t20 (bvxor s2 t19))
				(t21 (bvand s2 t19))
			)		
		(let
			(
				(s3 (bvxor c2 t14))
				(t16 (bvand c2 t14))
				(s5 (bvxor c5 t20))
				(t22 (bvand c5 t20))
			)		
		(let
			(
				(c3 (bvor t15 t16))
				(c6 (bvor t22 t21))
				(t24 (bvxor s3 t23))
				(t25 (bvand s3 t23))
				(p3 (bvxor s5 t35))
				(c10 (bvand s5 t35))
			)		
		(let
			(
				(s4 (bvxor t17 c3))
				(c4 (bvand t17 c3))
				(s6 (bvxor c6 t24))
				(t26 (bvand c6 t24))
			)		
		(let
			(
				(c7 (bvor t26 t25))
				(t28 (bvxor s4 t27))
				(t29 (bvand s4 t27))
				(t32 (bvxor c4 t31))
				(t33 (bvand c4 t31))
				(t37 (bvxor s6 t36))
				(t38 (bvand s6 t36))
			)		
		(let
			(
				(s7 (bvxor c7 t28))
				(t30 (bvand c7 t28))
				(s9 (bvxor c10 t37))
				(t39 (bvand c10 t37))
			)		
		(let
			(
				(c8 (bvor t30 t29))
				(c11 (bvor t39 t38))
				(t41 (bvxor s7 t40))
				(t42 (bvand s7 t40))
				(p4 (bvxor s9 t52))
				(c15 (bvand s9 t52))
			)		
		(let
			(
				(s8 (bvxor c8 t32))
				(t34 (bvand c8 t32))
				(s10 (bvxor c11 t41))
				(t43 (bvand c11 t41))
			)		
		(let
			(
				(c9 (bvor t34 t33))
				(c12 (bvor t43 t42))
				(t45 (bvxor s8 t44))
				(t46 (bvand s8 t44))
				(t54 (bvxor s10 t53))
				(t55 (bvand s10 t53))
			)		
		(let
			(
				(s11 (bvxor c12 t45))
				(t47 (bvand c12 t45))
				(t49 (bvxor c9 t48))
				(t50 (bvand c9 t48))
				(p5 (bvxor c15 t54))
				(t56 (bvand c15 t54))
			)		
		(let
			(
				(c13 (bvor t47 t46))
				(c16 (bvor t56 t55))
				(t58 (bvxor s11 t57))
				(t59 (bvand s11 t57))
			)		
		(let
			(
				(s12 (bvxor c13 t49))
				(t51 (bvand c13 t49))
				(p6 (bvxor c16 t58))
				(t60 (bvand c16 t58))
			)		
		(let
			(
				(c14 (bvor t51 t50))
				(c17 (bvor t60 t59))
				(t62 (bvxor s12 t61))
				(t63 (bvand s12 t61))
			)		
		(let
			(
				(p7 (bvxor c17 t62))
				(t64 (bvand c17 t62))
				(t66 (bvxor c14 t65))
				(t67 (bvand c14 t65))
			)		
		(let
			(
				(c18 (bvor t64 t63))
			)		
		(let
			(
				(p8 (bvxor c18 t66))
				(t68 (bvand c18 t66))
			)		
		(let
			(
				(p9 (bvor t68 t67))
			)
		(let
			(
				(x_t (concat (_ bv0 5) x4 x3 x2 x1 x0))
				(y_t (concat (_ bv0 5) y4 y3 y2 y1 y0))
			)
		(let 
			(
				(out_pchb (concat p9 p8 p7 p6 p5 p4 p3 p2 p1 p0))
				(out_sync (bvmul x_t y_t))
				
			)
			
		(= out_pchb out_sync))) )))))))))) )))))))))) ))
	)	
)
(check-sat)
(get-model)
(get-value (x4))
(get-value (x3))
(get-value (x2))
(get-value (x1))
(get-value (x0))
