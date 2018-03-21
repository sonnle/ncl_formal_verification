; Formal verification proof - input completeness of test_netlist10x10abs.txt
(set-logic QF_BV)

; Inputs: x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, y0, y1, y2, y3, y4, y5, y6, y7, y8, y9
(declare-fun x0 () (_ BitVec 1))
(declare-fun x1 () (_ BitVec 1))
(declare-fun x2 () (_ BitVec 1))
(declare-fun x3 () (_ BitVec 1))
(declare-fun x4 () (_ BitVec 1))
(declare-fun x5 () (_ BitVec 1))
(declare-fun x6 () (_ BitVec 1))
(declare-fun x7 () (_ BitVec 1))
(declare-fun x8 () (_ BitVec 1))
(declare-fun x9 () (_ BitVec 1))
(declare-fun y0 () (_ BitVec 1))
(declare-fun y1 () (_ BitVec 1))
(declare-fun y2 () (_ BitVec 1))
(declare-fun y3 () (_ BitVec 1))
(declare-fun y4 () (_ BitVec 1))
(declare-fun y5 () (_ BitVec 1))
(declare-fun y6 () (_ BitVec 1))
(declare-fun y7 () (_ BitVec 1))
(declare-fun y8 () (_ BitVec 1))
(declare-fun y9 () (_ BitVec 1))

(define-fun bvhasum ( (a (_ BitVec 1)) (b (_ BitVec 1))) (_ BitVec 1)
(bvxor a b) )	
(define-fun bvhacar ( (a (_ BitVec 1)) (b (_ BitVec 1))) (_ BitVec 1)
(bvand a b) )	
(define-fun bvfasum ( (a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1))) (_ BitVec 1)
(bvxor (bvxor a b) c ) )
(define-fun bvfacar ( (a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1))) (_ BitVec 1)
(bvor (bvor (bvand a b) (bvand a c)) (bvand b c)) )
; SAT/UNSAT assertion for test_netlist10x10abs.txt
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
				(t22 (bvand x6 y0))
				(t23 (bvand x5 y1))
				(t27 (bvand x7 y0))
				(t28 (bvand x6 y1))
				(t32 (bvand x8 y0))
				(t33 (bvand x7 y1))
				(t37 (bvand x9 y0))
				(t38 (bvand x8 y1))
				(t42 (bvand x9 y1))
				(t43 (bvand x0 y2))
				(t44 (bvand x1 y2))
				(t48 (bvand x2 y2))
				(t52 (bvand x3 y2))
				(t56 (bvand x4 y2))
				(t60 (bvand x5 y2))
				(t64 (bvand x6 y2))
				(t68 (bvand x7 y2))
				(t72 (bvand x8 y2))
				(t76 (bvand x9 y2))
				(t80 (bvand x0 y3))
				(t81 (bvand x1 y3))
				(t85 (bvand x2 y3))
				(t89 (bvand x3 y3))
				(t93 (bvand x4 y3))
				(t97 (bvand x5 y3))
				(t101 (bvand x6 y3))
				(t105 (bvand x7 y3))
				(t109 (bvand x8 y3))
				(t113 (bvand x9 y3))
				(t117 (bvand x0 y4))
				(t118 (bvand x1 y4))
				(t122 (bvand x2 y4))
				(t126 (bvand x3 y4))
				(t130 (bvand x4 y4))
				(t134 (bvand x5 y4))
				(t138 (bvand x6 y4))
				(t142 (bvand x7 y4))
				(t146 (bvand x8 y4))
				(t150 (bvand x9 y4))
				(t154 (bvand x0 y5))
				(t155 (bvand x1 y5))
				(t159 (bvand x2 y5))
				(t163 (bvand x3 y5))
				(t167 (bvand x4 y5))
				(t171 (bvand x5 y5))
				(t175 (bvand x6 y5))
				(t179 (bvand x7 y5))
				(t183 (bvand x8 y5))
				(t187 (bvand x9 y5))
				(t191 (bvand x0 y6))
				(t192 (bvand x1 y6))
				(t196 (bvand x2 y6))
				(t200 (bvand x3 y6))
				(t204 (bvand x4 y6))
				(t208 (bvand x5 y6))
				(t212 (bvand x6 y6))
				(t216 (bvand x7 y6))
				(t220 (bvand x8 y6))
				(t224 (bvand x9 y6))
				(t228 (bvand x0 y7))
				(t229 (bvand x1 y7))
				(t233 (bvand x2 y7))
				(t237 (bvand x3 y7))
				(t241 (bvand x4 y7))
				(t245 (bvand x5 y7))
				(t249 (bvand x6 y7))
				(t253 (bvand x7 y7))
				(t257 (bvand x8 y7))
				(t261 (bvand x9 y7))
				(t265 (bvand x0 y8))
				(t266 (bvand x1 y8))
				(t270 (bvand x2 y8))
				(t274 (bvand x3 y8))
				(t278 (bvand x4 y8))
				(t282 (bvand x5 y8))
				(t286 (bvand x6 y8))
				(t290 (bvand x7 y8))
				(t294 (bvand x8 y8))
				(t298 (bvand x9 y8))
				(t302 (bvand x0 y9))
				(t303 (bvand x1 y9))
				(t307 (bvand x2 y9))
				(t311 (bvand x3 y9))
				(t315 (bvand x4 y9))
				(t319 (bvand x5 y9))
				(t323 (bvand x6 y9))
				(t327 (bvand x7 y9))
				(t331 (bvand x8 y9))
				(t335 (bvand x9 y9))
			)		
		(let
			(
				(p1 (bvhasum t0 t1))
				(c0 (bvhacar t0 t1))
			)		
		(let
			(
				(s1 (bvfasum t2 t3 c0))
			)		
		(let
			(
				(c1 (bvfacar t2 t3 c0))
				(p2 (bvhasum s1 t43))
				(c10 (bvhacar s1 t43))
			)		
		(let
			(
				(s2 (bvfasum t7 t8 c1))
			)		
		(let
			(
				(c1 (bvfacar t7 t8 c1))
			)		
		(let
			(
				(s3 (bvfasum t12 t13 c2))
				(s10 (bvfasum s2 t44 c10))
			)		
		(let
			(
				(c3 (bvfacar t12 t13 c2))
				(c11 (bvfacar s2 t44 c10))
				(p3 (bvhasum s10 t80))
				(c20 (bvhacar s10 t80))
			)		
		(let
			(
				(s4 (bvfasum t17 t18 c3))
				(s11 (bvfasum s3 t48 c11))
			)		
		(let
			(
				(c4 (bvfacar t17 t18 c3))
				(c12 (bvfacar s3 t48 c11))
			)		
		(let
			(
				(s5 (bvfasum t22 t23 c4))
				(s12 (bvfasum s4 t52 c12))
				(s19 (bvfasum s11 t81 c20))
			)		
		(let
			(
				(c5 (bvfacar t22 t23 c4))
				(c13 (bvfacar s4 t52 c12))
				(c21 (bvfacar s11 t81 c20))
				(p4 (bvhasum s19 t117))
				(c30 (bvhacar s19 t117))
			)		
		(let
			(
				(s6 (bvfasum t27 t28 c5))
				(s13 (bvfasum s5 t56 c13))
				(s20 (bvfasum s12 t85 c21))
			)		
		(let
			(
				(c6 (bvfacar t27 t28 c5))
				(c14 (bvfacar s5 t56 c13))
				(c22 (bvfacar s12 t85 c21))
			)		
		(let
			(
				(s7 (bvfasum t32 t33 c6))
				(s14 (bvfasum s6 t60 c14))
				(s21 (bvfasum s13 t89 c22))
				(s28 (bvfasum s20 t118 c30))
			)		
		(let
			(
				(c7 (bvfacar t32 t33 c6))
				(c15 (bvfacar s6 t60 c14))
				(c23 (bvfacar s13 t89 c22))
				(c31 (bvfacar s20 t118 c30))
				(p5 (bvhasum s28 t154))
				(c40 (bvhacar s28 t154))
			)		
		(let
			(
				(s8 (bvfasum t37 t38 c7))
				(s15 (bvfasum s7 t64 c15))
				(s22 (bvfasum s14 t93 c23))
				(s29 (bvfasum s21 t122 c31))
			)		
		(let
			(
				(c8 (bvfacar t37 t38 c7))
				(c16 (bvfacar s7 t64 c15))
				(c24 (bvfacar s14 t93 c23))
				(c32 (bvfacar s21 t122 c31))
			)		
		(let
			(
				(s9 (bvhasum c8 t42))
				(c9 (bvhacar c8 t42))
				(s16 (bvfasum s8 t68 c16))
				(s23 (bvfasum s15 t97 c24))
				(s30 (bvfasum s22 t126 c32))
				(s37 (bvfasum s29 t155 c40))
			)		
		(let
			(
				(c17 (bvfacar s8 t68 c16))
				(c25 (bvfacar s15 t97 c24))
				(c33 (bvfacar s22 t126 c32))
				(c41 (bvfacar s29 t155 c40))
				(p6 (bvhasum s37 t191))
				(c50 (bvhacar s37 t191))
			)		
		(let
			(
				(s17 (bvfasum s9 t72 c17))
				(s24 (bvfasum s16 t101 c25))
				(s31 (bvfasum s23 t130 c33))
				(s38 (bvfasum s30 t159 c41))
			)		
		(let
			(
				(c18 (bvfacar s9 t72 c17))
				(c26 (bvfacar s16 t101 c25))
				(c34 (bvfacar s23 t130 c33))
				(c42 (bvfacar s30 t159 c41))
			)		
		(let
			(
				(s18 (bvfasum c9 t76 c18))
				(s25 (bvfasum s17 t105 c26))
				(s32 (bvfasum s24 t134 c34))
				(s39 (bvfasum s31 t163 c42))
				(s46 (bvfasum s38 t192 c50))
			)		
		(let
			(
				(c19 (bvfacar c9 t76 c18))
				(c27 (bvfacar s17 t105 c26))
				(c35 (bvfacar s24 t134 c34))
				(c43 (bvfacar s31 t163 c42))
				(c51 (bvfacar s38 t192 c50))
				(p7 (bvhasum s46 t228))
				(c60 (bvhacar s46 t228))
			)		
		(let
			(
				(s26 (bvfasum s18 t109 c27))
				(s33 (bvfasum s25 t138 c35))
				(s40 (bvfasum s32 t167 c43))
				(s47 (bvfasum s39 t196 c51))
			)		
		(let
			(
				(c28 (bvfacar s18 t109 c27))
				(c36 (bvfacar s25 t138 c35))
				(c44 (bvfacar s32 t167 c43))
				(c52 (bvfacar s39 t196 c51))
			)		
		(let
			(
				(s27 (bvfasum c19 t113 c28))
				(s34 (bvfasum s26 t142 c36))
				(s41 (bvfasum s33 t171 c44))
				(s48 (bvfasum s40 t200 c52))
				(s55 (bvfasum s47 t229 c60))
			)		
		(let
			(
				(c29 (bvfacar c19 t113 c28))
				(c37 (bvfacar s26 t142 c36))
				(c45 (bvfacar s33 t171 c44))
				(c53 (bvfacar s40 t200 c52))
				(c61 (bvfacar s47 t229 c60))
				(p8 (bvhasum s55 t265))
				(c70 (bvhacar s55 t265))
			)		
		(let
			(
				(s35 (bvfasum s27 t146 c37))
				(t151 (bvxor c29 t150))
				(s42 (bvfasum s34 t175 c45))
				(s49 (bvfasum s41 t204 c53))
				(s56 (bvfasum s48 t233 c61))
			)		
		(let
			(
				(c38 (bvfacar s27 t146 c37))
				(c46 (bvfacar s34 t175 c45))
				(c54 (bvfacar s41 t204 c53))
				(c62 (bvfacar s48 t233 c61))
			)		
		(let
			(
				(s36 (bvfasum c29 t150 c38))
				(s43 (bvfasum s35 t179 c46))
				(s50 (bvfasum s42 t208 c54))
				(s57 (bvfasum s49 t237 c62))
				(s64 (bvfasum s56 t266 c70))
			)		
		(let
			(
				(c39 (bvfacar c29 t150 c38))
				(c47 (bvfacar s35 t179 c46))
				(c55 (bvfacar s42 t208 c54))
				(c63 (bvfacar s49 t237 c62))
				(c71 (bvfacar s56 t266 c70))
				(p9 (bvhasum s64 t302))
				(c80 (bvhacar s64 t302))
			)		
		(let
			(
				(s44 (bvfasum s36 t183 c47))
				(s51 (bvfasum s43 t212 c55))
				(s58 (bvfasum s50 t241 c63))
				(s65 (bvfasum s57 t270 c71))
			)		
		(let
			(
				(c48 (bvfacar s36 t183 c47))
				(c56 (bvfacar s43 t212 c55))
				(c64 (bvfacar s50 t241 c63))
				(c72 (bvfacar s57 t270 c71))
			)		
		(let
			(
				(s45 (bvfasum c39 t187 c48))
				(s52 (bvfasum s44 t216 c56))
				(s59 (bvfasum s51 t245 c64))
				(s66 (bvfasum s58 t274 c72))
				(p10 (bvfasum s65 t303 c80))
			)		
		(let
			(
				(c49 (bvfacar c39 t187 c48))
				(c57 (bvfacar s44 t216 c56))
				(c65 (bvfacar s51 t245 c64))
				(c73 (bvfacar s58 t274 c72))
				(c81 (bvfacar s65 t303 c80))
			)		
		(let
			(
				(s53 (bvfasum s45 t220 c57))
				(s60 (bvfasum s52 t249 c65))
				(s67 (bvfasum s59 t278 c73))
				(p11 (bvfasum s66 t307 c81))
			)		
		(let
			(
				(c58 (bvfacar s45 t220 c57))
				(c66 (bvfacar s52 t249 c65))
				(c74 (bvfacar s59 t278 c73))
				(c82 (bvfacar s66 t307 c81))
			)		
		(let
			(
				(s54 (bvfasum c49 t224 c58))
				(s61 (bvfasum s53 t253 c66))
				(s68 (bvfasum s60 t282 c74))
				(p12 (bvfasum s67 t311 c82))
			)		
		(let
			(
				(c59 (bvfacar c49 t224 c58))
				(c67 (bvfacar s53 t253 c66))
				(c75 (bvfacar s60 t282 c74))
				(c83 (bvfacar s67 t311 c82))
			)		
		(let
			(
				(s62 (bvfasum s54 t257 c67))
				(s69 (bvfasum s61 t286 c75))
				(p13 (bvfasum s68 t315 c83))
			)		
		(let
			(
				(c68 (bvfacar s54 t257 c67))
				(c76 (bvfacar s61 t286 c75))
				(c84 (bvfacar s68 t315 c83))
			)		
		(let
			(
				(s63 (bvfasum c59 t261 c68))
				(s70 (bvfasum s62 t290 c76))
				(p14 (bvfasum s69 t319 c84))
			)		
		(let
			(
				(c69 (bvfacar c59 t261 c68))
				(c77 (bvfacar s62 t290 c76))
				(c85 (bvfacar s69 t319 c84))
			)		
		(let
			(
				(s71 (bvfasum s63 t294 c77))
				(p15 (bvfasum s70 t323 c85))
			)		
		(let
			(
				(c78 (bvfacar s63 t294 c77))
				(c86 (bvfacar s70 t323 c85))
			)		
		(let
			(
				(s72 (bvfasum c69 t298 c78))
				(p16 (bvfasum s71 t327 c86))
			)		
		(let
			(
				(c79 (bvfacar c69 t298 c78))
				(c87 (bvfacar s71 t327 c86))
			)		
		(let
			(
				(p17 (bvfasum s72 t331 c87))
			)		
		(let
			(
				(c88 (bvfacar s72 t331 c87))
			)		
		(let
			(
				(p18 (bvfasum c79 t335 c88))
			)		
		(let
			(
				(p19 (bvfacar c79 t335 c88))
			)
		(let
			(
				(x_t (concat (_ bv0 10) x9 x8 x7 x6 x5 x4 x3 x2 x1 x0))
				(y_t (concat (_ bv0 10) y9 y8 y7 y6 y5 y4 y3 y2 y1 y0))
			)
		(let 
			(
				(out_pchb (concat p19 p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0))
				(out_sync (bvmul x_t y_t))
				
			)
			
		(= out_pchb out_sync))) )))))))))) )))))))))) )))))))))) )))))))))) )))))))))) ))
	)	
)
(check-sat)
(get-model)