; Formal verification proof - SCLBool with Bool Specification of test_netlist_4+2x2MAC.txt (with 2 stages)
(set-logic QF_BV)

; Inputs: xi0, xi1,yi0, yi1
(declare-fun Xi0 () (_ BitVec 2))
(declare-fun Xi1 () (_ BitVec 2))
(declare-fun Yi0 () (_ BitVec 2))
(declare-fun Yi1 () (_ BitVec 2))

; Outputs: acci0, acci1, acci2, acci3
(declare-fun acci0 () (_ BitVec 2))
(declare-fun acci1 () (_ BitVec 2))
(declare-fun acci2 () (_ BitVec 2))
(declare-fun acci3 () (_ BitVec 2))

(declare-fun reset () (_ BitVec 1))
(declare-fun Ki () (_ BitVec 1))
(declare-fun Ki1 () (_ BitVec 1))
(declare-fun Ki2 () (_ BitVec 1))
(declare-fun Ki3 () (_ BitVec 1))
(declare-fun gc () (_ BitVec 1))
(declare-fun cs () (_ BitVec 2))
(declare-fun cs1 () (_ BitVec 2))

; NCL Gate Boolean Function - TH12: (A + B)
(define-fun th12 ((a (_ BitVec 1)) (b (_ BitVec 1)) (gl (_ BitVec 1)) ) (_ BitVec 1)
    (bvor a b)
)	
; NCL Gate Boolean Function - TH22: (AB)
(define-fun th22 ((a (_ BitVec 1)) (b (_ BitVec 1)) (gl (_ BitVec 1)) ) (_ BitVec 1)
(bvand a b)
)
; NCL Gate Boolean Function - TH23: (AB + AC + BC)
(define-fun th23 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (gl (_ BitVec 1)) ) (_ BitVec 1)
	(bvor (bvand a b) (bvor (bvand a c) (bvand b c)) )
)	
; NCL Gate Boolean Function - THand0: (AB + BC + AD)
(define-fun thand0 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
	(bvor (bvand a b) (bvor (bvand b c) (bvand a d)) )
)
; NCL Gate Boolean Function - TH24comp: (AC + BC + AD + BD)
(define-fun th24comp ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
	(bvor (bvand a c) (bvor (bvand b c) (bvor (bvand a d) (bvand b d)) ) )
)
; NCL Gate Boolean Function - TH34w2: (AB + AC + AD + BCD)
(define-fun th34w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
	(bvor (bvand a b) (bvor (bvand a c) (bvor (bvand a d) (bvand b (bvand c d)) ) ) )
)	
; Extract Function of rail0 of a dual rail signal
(define-fun rail0 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 0 0) a)
)

; Extract Function rail1 of a dual rail signal
(define-fun rail1 ((a (_ BitVec 2))) (_ BitVec 1)
    ((_ extract 1 1) a)
)
; Extract Function Ko output of a register
(define-fun Ko_op ((a (_ BitVec 3))) (_ BitVec 1)
    ((_ extract 2 2) a)
)
; Extract Function data output of a register Q1Q0
(define-fun data_op ((a (_ BitVec 3))) (_ BitVec 2)
    ((_ extract 1 0) a)
)

; NCL reset-to-NULL register Function
(define-fun Reg_NULL ((D (_ BitVec 2)) (Ki (_ BitVec 1)) (reset (_ BitVec 1)) (cs (_ BitVec 2))) (_ BitVec 2)
	(ite (= reset (_ bv0 1)) 
				(ite (= Ki (_ bv1 1)) D cs )
		(_ bv0 2) 
	)
)

; NCL reset-to-DATA0 register Function
(define-fun Reg_DATA0 ((D (_ BitVec 2)) (Ki (_ BitVec 1)) (reset (_ BitVec 1)) (cs (_ BitVec 2))) (_ BitVec 2)
	(ite (= reset (_ bv0 1)) 
				(ite (= Ki (_ bv1 1)) D cs )
		(_ bv1 2) 
	)
)

; sync reset-to-0 register Function
(define-fun sync_Reg0 ((D (_ BitVec 1)) (enable (_ BitVec 1)) (reset (_ BitVec 1)) (cs (_ BitVec 1))) (_ BitVec 1)
	(ite (= reset (_ bv0 1))
		(ite (= enable (_ bv1 1)) 
			D cs)
		(_ bv0 1)
	)
)

; sync Half-Adder Function - carry
(define-fun sync_HA_carry ((x (_ BitVec 1)) (y (_ BitVec 1))) (_ BitVec 1)
	(bvand x y)
)

; sync Half-Adder Function - sum
(define-fun sync_HA_sum ((x (_ BitVec 1)) (y (_ BitVec 1))) (_ BitVec 1)
	(bvxor x y)
)

; sync Full-Adder Function - carry
(define-fun sync_FA_carry ((x (_ BitVec 1)) (y (_ BitVec 1)) (cin (_ BitVec 1))) (_ BitVec 1)
	(bvor (bvand cin (bvxor x y)) (bvand x y))
)

; sync Full-Adder Function - sum
(define-fun sync_FA_sum((x (_ BitVec 1)) (y (_ BitVec 1)) (cin (_ BitVec 1))) (_ BitVec 1)
	(bvxor cin (bvxor x y))
)

; Determine if the dual rail signal is null (0b00)
(define-fun nullp ((a (_ BitVec 2))) (Bool)
    (= (_ bv0 2) a)
)
; Determine if the dual rail signal is data (0b01 OR 0b10)
(define-fun datap ((a (_ BitVec 2))) (Bool)
    (or
        (= (_ bv1 2) a)
        (= (_ bv2 2) a)
    )
) 	

; SAT/UNSAT assertion for test_netlist_12+6x6MAC.txt
(assert
	(not
		(let
			(
				(x0 (Reg_NULL Xi0 Ki reset cs))
				(x1 (Reg_NULL Xi1 Ki reset cs))
				(y0 (Reg_NULL Yi0 Ki reset cs))
				(y1 (Reg_NULL Yi1 Ki reset cs))
				(acc0 (Reg_NULL acci0 Ki reset cs))
				(acc1 (Reg_NULL acci1 Ki reset cs))
				(acc2 (Reg_NULL acci2 Ki reset cs))
				(acc3 (Reg_NULL acci3 Ki reset cs))				
			)
		(let
			(
				(t0_1 (th22 (rail1 x0)  (rail1 y0) gc))
				(t0_0 (th12 (rail0 x0)  (rail0 y0) gc))
				(t1_1 (th22 (rail1 x1)  (rail1 y0) gc))
				(t1_0 (th12 (rail0 x1)  (rail0 y0) gc))
				(t2_1 (th22 (rail1 x0)  (rail1 y1) gc))
				(t2_0 (th12 (rail0 x0)  (rail0 y1) gc))
				(t3_1 (th22 (rail1 x1)  (rail1 y1) gc))
				(t3_0 (th12 (rail0 x1)  (rail0 y1) gc))
			)		
		(let
			(
				(t4_1 (th24comp t1_0  t2_0  t1_1  t2_1 gc))
				(t4_0 (th24comp t1_0  t2_1  t2_0  t1_1 gc))
				(c0_0 (th12 t1_0  t2_0 gc))
				(c0_1 (th22 t1_1  t2_1 gc))
				(c1_1 (th22 t0_1  (rail1 acc0) gc))
				(c1_0 (th12 t0_0  (rail0 acc0) gc))
				(t5_1 (th24comp t0_0  (rail0 acc0)  t0_1  (rail1 acc0) gc))
				(t5_0 (th24comp t0_0  (rail1 acc0)  (rail0 acc0)  t0_1 gc))
			)		
		(let
			(
				(t6_1 (th24comp t4_0  (rail0 acc1)  t4_1  (rail1 acc1) gc))
				(t6_0 (th24comp t4_0  (rail1 acc1)  (rail0 acc1)  t4_1 gc))
				(c2_0 (th12 t4_0  (rail0 acc1) gc))
				(c2_1 (th22 t4_1  (rail1 acc1) gc))
			)		
		(let
			(
				(c3_0 (th23 t3_0  (rail0 acc2)  c0_0 gc))
				(c3_1 (th23 t3_1  (rail1 acc2)  c0_1 gc))
				
			)		
		(let
			(
				(t7_0 (th34w2 c3_1 t3_0 (rail0 acc2) c0_0 gc))
				(t7_1 (th34w2 c3_0 t3_1 (rail1 acc2) c0_1 gc))
				
			)	
		(let
			(
				(r0 (Reg_NULL (concat t5_1 t5_0) Ki1 reset cs))
				(r1 (Reg_NULL (concat c1_1 c1_0) Ki1 reset cs))
				(r2 (Reg_NULL (concat t6_1 t6_0) Ki1 reset cs))
				(r3 (Reg_NULL (concat c2_1 c2_0) Ki1 reset cs))
				(r4 (Reg_NULL (concat t7_1 t7_0) Ki1 reset cs))
				(r5 (Reg_NULL (concat c3_1 c3_0) Ki1 reset cs))
				(r6 (Reg_NULL acc3 Ki1 reset cs))
			)
		(let
			(
				(t8_1 (th24comp (rail0 r1) (rail0 r2) (rail1 r1) (rail1 r2) gc))
				(t8_0 (th24comp (rail0 r1) (rail1 r2) (rail0 r2) (rail1 r1) gc))
				(c4_0 (th12 (rail0 r1) (rail0 r2) gc))
				(c4_1 (th22 (rail1 r1) (rail1 r2) gc))
			)		
		(let
			(
			
				(c5_0 (th23 (rail0 r3)  (rail0 r4)  c4_0 gc))
				(c5_1 (th23 (rail1 r3)  (rail1 r4)  c4_1 gc))
			)
		(let 
			(
				(t9_0 (th34w2 c5_1  (rail0 r3)  (rail0 r4)  c4_0 gc))
				(t9_1 (th34w2 c5_0  (rail1 r3)  (rail1 r4)  c4_1 gc))
				(c6_0 (th23 (rail0 r5)  (rail0 r6)  c5_0 gc))
				(c6_1 (th23 (rail1 r5)  (rail1 r6)  c5_1 gc))
			)
		(let
			(
				(t10_0 (th34w2 c6_1  (rail0 r5)  (rail0 r6)  c5_0 gc))
				(t10_1 (th34w2 c6_0  (rail1 r5)  (rail1 r6)  c5_1 gc))
			)
		(let
			(
				(p0 (Reg_NULL r0 Ki2 reset cs))
				(p1 (Reg_NULL (concat t8_1 t8_0) Ki2 reset cs))
				(p2 (Reg_NULL (concat t9_1 t9_0) Ki2 reset cs))
				(p3 (Reg_NULL (concat t10_1 t10_0) Ki2 reset cs))
			)
		(let
			(
				(acc0_1 (Reg_DATA0 p0 Ki3 reset cs1))
				(acc1_1 (Reg_DATA0 p1 Ki3 reset cs1))
				(acc2_1 (Reg_DATA0 p2 Ki3 reset cs1))
				(acc3_1 (Reg_DATA0 p3 Ki3 reset cs1))
			)
		(let
			(
				(t0_sync (bvand (rail1 Xi0) (rail1 Yi0)))
				(t1_sync (bvand (rail1 Xi0) (rail1 Yi1)))
				(t2_sync (bvand (rail1 Xi1) (rail1 Yi0)))
				(t3_sync (bvand (rail1 Xi1) (rail1 Yi1)))
			)
		(let
			(
				(c1_sync (sync_HA_carry (rail1 acc0) t0_sync))
				(t5_sync (sync_HA_sum (rail1 acc0) t0_sync))
				(c0_sync (sync_HA_carry t1_sync t2_sync))
				(t4_sync (sync_HA_sum t1_sync t2_sync))
			)
		(let
			(
				(c2_sync (sync_HA_carry (rail1 acc1) t4_sync))
				(t6_sync (sync_HA_sum (rail1 acc1) t4_sync))
				(c3_sync (sync_FA_carry (rail1 acc2) c0_sync t3_sync))
				(t7_sync (sync_FA_sum (rail1 acc2) c0_sync t3_sync))
			)
		(let
			(
				(c4_sync (sync_HA_carry c1_sync t6_sync))
				(t8_sync (sync_HA_sum c1_sync t6_sync))
			)
		(let
			(
				(c5_sync (sync_FA_carry c4_sync c2_sync t7_sync))
				(t9_sync (sync_FA_sum c4_sync c2_sync t7_sync))
			)
		(let
			(
				(c6_sync (sync_FA_carry c5_sync c3_sync (rail1 acc3)))
				(t10_sync (sync_FA_sum c5_sync c3_sync (rail1 acc3)))
			)
		(let
			(
				(acc0_1_sync (sync_Reg0 t5_sync Ki3 reset (rail1 cs1)))
				(acc1_1_sync (sync_Reg0 t8_sync Ki3 reset (rail1 cs1)))
				(acc2_1_sync (sync_Reg0 t9_sync Ki3 reset (rail1 cs1)))
				(acc3_1_sync (sync_Reg0 t10_sync Ki3 reset (rail1 cs1)))
			)
		(=>
			(and
				(= (_ bv0 1) gc)
				(= (_ bv1 1) Ki)
				(= (_ bv1 1) Ki1)
				(= (_ bv1 1) Ki2)
				(= (_ bv1 1) Ki3)
				(datap Xi0)
				(datap Xi1)
				(datap Yi0)
				(datap Yi1)
				(datap acc0)
				(datap acc1)
				(datap acc2)
				(datap acc3)
			)
			(and
				(= (rail1 acc0_1) acc0_1_sync)
				(= (rail1 acc1_1) acc1_1_sync)
				(= (rail1 acc2_1) acc2_1_sync)
				(= (rail1 acc3_1) acc3_1_sync)
			)
		)))))))))))))))))))))
	)
)

(check-sat)
(get-model)
