; Formal verification proof - input completeness of test_netlist6x6.txt
(set-logic QF_BV)

; Inputs: x0, x1, x2, x3, x4, x5, y0, y1, y2, y3, y4, y5
(declare-fun x0 () (_ BitVec 1))
(declare-fun x1 () (_ BitVec 1))
(declare-fun x2 () (_ BitVec 1))
(declare-fun x3 () (_ BitVec 1))
(declare-fun x4 () (_ BitVec 1))
(declare-fun x5 () (_ BitVec 1))
(declare-fun y0 () (_ BitVec 1))
(declare-fun y1 () (_ BitVec 1))
(declare-fun y2 () (_ BitVec 1))
(declare-fun y3 () (_ BitVec 1))
(declare-fun y4 () (_ BitVec 1))
(declare-fun y5 () (_ BitVec 1))

; Outputs: p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11
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
(declare-fun p10 () (_ BitVec 1))
(declare-fun p11 () (_ BitVec 1))

; SAT/UNSAT assertion for test_netlist6x6.txt
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
				(t17 (bvand x5 y0))
				(t18 (bvand x4 y1))
				(t22 (bvand x5 y1))
				(t23 (bvand x0 y2))
				(t24 (bvand x1 y2))
				(t28 (bvand x2 y2))
				(t32 (bvand x3 y2))
				(t36 (bvand x4 y2))
				(t40 (bvand x5 y2))
				(t44 (bvand x0 y3))
				(t45 (bvand x1 y3))
				(t49 (bvand x2 y3))
				(t53 (bvand x3 y3))
				(t57 (bvand x4 y3))
				(t61 (bvand x5 y3))
				(t65 (bvand x0 y4))
				(t66 (bvand x1 y4))
				(t70 (bvand x2 y4))
				(t74 (bvand x3 y4))
				(t78 (bvand x4 y4))
				(t82 (bvand x5 y4))
				(t86 (bvand x0 y5))
				(t87 (bvand x1 y5))
				(t91 (bvand x2 y5))
				(t95 (bvand x3 y5))
				(t99 (bvand x4 y5))
				(t103 (bvand x5 y5))
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
				(t19 (bvxor t17 t18))
				(t20 (bvand t17 t18))
			)		
		(let
			(
				(s1 (bvxor c0 t4))
				(t5 (bvand c0 t4))
			)		
		(let
			(
				(c1 (bvor t6 t5))
				(p2 (bvxor s1 t23))
				(c6 (bvand s1 t23))
			)		
		(let
			(
				(s2 (bvxor c1 t9))
				(t11 (bvand c1 t9))
			)		
		(let
			(
				(c2 (bvor t10 t11))
				(t25 (bvxor s2 t24))
				(t26 (bvand s2 t24))
			)		
		(let
			(
				(s3 (bvxor c2 t14))
				(t16 (bvand c2 t14))
				(s6 (bvxor c6 t25))
				(t27 (bvand c6 t25))
			)		
		(let
			(
				(c3 (bvor t15 t16))
				(c7 (bvor t27 t26))
				(t29 (bvxor s3 t28))
				(t30 (bvand s3 t28))
				(p3 (bvxor s6 t44))
				(c12 (bvand s6 t44))
			)		
		(let
			(
				(s4 (bvxor c3 t19))
				(t21 (bvand c3 t19))
				(s7 (bvxor c7 t29))
				(t31 (bvand c7 t29))
			)		
		(let
			(
				(c4 (bvor t21 t20))
				(c8 (bvor t31 t30))
				(t33 (bvxor s4 t32))
				(t34 (bvand s4 t32))
				(t46 (bvxor s7 t45))
				(t47 (bvand s7 t45))
			)		
		(let
			(
				(s5 (bvxor c4 t22))
				(c5 (bvand c4 t22))
				(s8 (bvxor c8 t33))
				(t35 (bvand c8 t33))
				(s11 (bvxor c12 t46))
				(t48 (bvand c12 t46))
			)		
		(let
			(
				(c9 (bvor t35 t34))
				(t37 (bvxor s5 t36))
				(t38 (bvand s5 t36))
				(t41 (bvxor c5 t40))
				(t42 (bvand c5 t40))
				(c13 (bvor t48 t47))
				(t50 (bvxor s8 t49))
				(t51 (bvand s8 t49))
				(p4 (bvxor s11 t65))
				(c18 (bvand s11 t65))
			)		
		(let
			(
				(s9 (bvxor c9 t37))
				(t39 (bvand c9 t37))
				(s12 (bvxor c13 t50))
				(t52 (bvand c13 t50))
			)		
		(let
			(
				(c10 (bvor t39 t38))
				(c14 (bvor t52 t51))
				(t54 (bvxor s9 t53))
				(t55 (bvand s9 t53))
				(t67 (bvxor s12 t66))
				(t68 (bvand s12 t66))
			)		
		(let
			(
				(s10 (bvxor c10 t41))
				(t43 (bvand c10 t41))
				(s13 (bvxor c14 t54))
				(t56 (bvand c14 t54))
				(s16 (bvxor c18 t67))
				(t69 (bvand c18 t67))
			)		
		(let
			(
				(c11 (bvor t43 t42))
				(c15 (bvor t56 t55))
				(t58 (bvxor s10 t57))
				(t59 (bvand s10 t57))
				(c19 (bvor t69 t68))
				(t71 (bvxor s13 t70))
				(t72 (bvand s13 t70))
				(p5 (bvxor s16 t86))
				(c24 (bvand s16 t86))
			)		
		(let
			(
				(s14 (bvxor c15 t58))
				(t60 (bvand c15 t58))
				(t62 (bvxor c11 t61))
				(t63 (bvand c11 t61))
				(s17 (bvxor c19 t71))
				(t73 (bvand c19 t71))
			)		
		(let
			(
				(c16 (bvor t60 t59))
				(c20 (bvor t73 t72))
				(t75 (bvxor s14 t74))
				(t76 (bvand s14 t74))
				(t88 (bvxor s17 t87))
				(t89 (bvand s17 t87))
			)		
		(let
			(
				(s15 (bvxor c16 t62))
				(t64 (bvand c16 t62))
				(s18 (bvxor c20 t75))
				(t77 (bvand c20 t75))
				(p6 (bvxor c24 t88))
				(t90 (bvand c24 t88))
			)		
		(let
			(
				(c17 (bvor t64 t63))
				(c21 (bvor t77 t76))
				(t79 (bvxor s15 t78))
				(t80 (bvand s15 t78))
				(c25 (bvor t90 t89))
				(t92 (bvxor s18 t91))
				(t93 (bvand s18 t91))
			)		
		(let
			(
				(s19 (bvxor c21 t79))
				(t81 (bvand c21 t79))
				(t83 (bvxor c17 t82))
				(t84 (bvand c17 t82))
				(p7 (bvxor c25 t92))
				(t94 (bvand c25 t92))
			)		
		(let
			(
				(c22 (bvor t81 t80))
				(c26 (bvor t94 t93))
				(t96 (bvxor s19 t95))
				(t97 (bvand s19 t95))
			)		
		(let
			(
				(s20 (bvxor c22 t83))
				(t85 (bvand c22 t83))
				(p8 (bvxor c26 t96))
				(t98 (bvand c26 t96))
			)		
		(let
			(
				(c23 (bvor t85 t84))
				(c27 (bvor t98 t97))
				(t100 (bvxor s20 t99))
				(t101 (bvand s20 t99))
			)		
		(let
			(
				(p9 (bvxor c27 t100))
				(t102 (bvand c27 t100))
				(t104 (bvxor c23 t103))
				(t105 (bvand c23 t103))
			)		
		(let
			(
				(c28 (bvor t102 t101))
			)		
		(let
			(
				(p10 (bvxor c28 t104))
				(t106 (bvand c28 t104))
			)		
		(let
			(
				(p11 (bvor t106 t105))
			)
		(let
			(
				(x_t (concat (_ bv0 6) x5 x4 x3 x2 x1 x0))
				(y_t (concat (_ bv0 6) y5 y4 y3 y2 y1 y0))
			)
		(let 
			(
				(out_pchb (concat p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0))
				(out_sync (bvmul x_t y_t))
				
			)
			
		(= out_pchb out_sync))) )))))))))) )))))))))) ))))))))
	)	
)
(check-sat)
(get-model)
