; Formal verification proof - SCLBool with Bool Specification of test_netlist_4+2x2MAC.txt (with 2 stages)
(set-logic QF_BV)

(declare-fun Xi0 () (_ BitVec 2))
(declare-fun Xi1 () (_ BitVec 2))
(declare-fun Xi2 () (_ BitVec 2))
(declare-fun Xi3 () (_ BitVec 2))
(declare-fun Yi0 () (_ BitVec 2))
(declare-fun Yi1 () (_ BitVec 2))
(declare-fun Yi2 () (_ BitVec 2))
(declare-fun Yi3 () (_ BitVec 2))

(declare-fun acci0 () (_ BitVec 2))
(declare-fun acci1 () (_ BitVec 2))
(declare-fun acci2 () (_ BitVec 2))
(declare-fun acci3 () (_ BitVec 2))
(declare-fun acci4 () (_ BitVec 2))
(declare-fun acci5 () (_ BitVec 2))
(declare-fun acci6 () (_ BitVec 2))
(declare-fun acci7 () (_ BitVec 2))

(declare-fun reset () (_ BitVec 1))
(declare-fun Ki0 () (_ BitVec 1))
(declare-fun Ki1 () (_ BitVec 1))
(declare-fun Gc_0 () (_ BitVec 1))
(declare-fun cs0 () (_ BitVec 2))
(declare-fun cs1 () (_ BitVec 2))

(declare-fun o_sync () (_ BitVec 8))
(declare-fun o_ncl () (_ BitVec 8))
(declare-fun i_x () (_ BitVec 4))
(declare-fun i_y () (_ BitVec 4))
(declare-fun i_acc () (_ BitVec 8))
(declare-fun o_z () (_ BitVec 8))



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

; NCL Full-Adder
; The output will be concatenated as follows:        | variable - S1, S0, Cout1, Cout0
;                                                    |      bit -  3,  2,     1,     0
; The last gate values (gl) will be used as follows: | variable -        gl_3,        gl_2,         gl_1,         gl_0
;                                                    |     gate - th23 rail 0, th23 rail 1, th35w2 rail0, th35w2 rail1
(define-fun ncl_fa ((x (_ BitVec 2)) (y (_ BitVec 2)) (cin (_ BitVec 2)) (gl (_ BitVec 1))) (_ BitVec 4)
    (let
        (
            (gn_0 (th23 (rail0 x) (rail0 y) (rail0 cin) gl))
            (gn_1 (th23 (rail1 x) (rail1 y) (rail1 cin) gl))
        )
    (let
        (
            (gn_2 (th34w2 gn_1 (rail0 x) (rail0 y) (rail0 cin) gl))
            (gn_3 (th34w2 gn_0 (rail1 x) (rail1 y) (rail1 cin) gl))
        )
    (concat gn_3 gn_2 gn_1 gn_0)))
)

; NCL Half-Adder
; The output will be concatenated as follows:        | variable - S1, S0, Cout1, Cout0
;                                                    |      bit -  3,  2,     1,     0
; The last gate values (gl) will be used as follows: | variable -      gl_3,      gl_2, gl_1, gl_0
;                                                    |     gate - th24comp0, th24comp1, th12, th22
(define-fun ncl_ha ((x (_ BitVec 2)) (y (_ BitVec 2)) (gl (_ BitVec 1))) (_ BitVec 4)
    (concat
        (th24comp (rail0 y) (rail0 x) (rail1 y) (rail1 x) gl)
        (th24comp (rail0 y) (rail1 x) (rail0 x) (rail1 y) gl)
        (th22 (rail1 y) (rail1 x) gl)
        (th12 (rail0 y) (rail0 x) gl))
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
				(X0 (Reg_NULL Xi0 Ki0 reset cs0))
				(X1 (Reg_NULL Xi1 Ki0 reset cs0))
				(X2 (Reg_NULL Xi2 Ki0 reset cs0))
				(X3 (Reg_NULL Xi3 Ki0 reset cs0))
				(Y0 (Reg_NULL Yi0 Ki0 reset cs0))
				(Y1 (Reg_NULL Yi1 Ki0 reset cs0))
				(Y2 (Reg_NULL Yi2 Ki0 reset cs0))
				(Y3 (Reg_NULL Yi3 Ki0 reset cs0))
				(ACC0 (Reg_NULL acci0 Ki0 reset cs0))
				(ACC1 (Reg_NULL acci1 Ki0 reset cs0))
				(ACC2 (Reg_NULL acci2 Ki0 reset cs0))
				(ACC3 (Reg_NULL acci3 Ki0 reset cs0))
				(ACC4 (Reg_NULL acci4 Ki0 reset cs0))
				(ACC5 (Reg_NULL acci5 Ki0 reset cs0))
				(ACC6 (Reg_NULL acci6 Ki0 reset cs0))
				(ACC7 (Reg_NULL acci7 Ki0 reset cs0))
			)
		(let
			(
				(and0x2_0 (th12 (rail0 X0) (rail0 Y2) Gc_0))
				(and0x2_1 (th22 (rail1 X0) (rail1 Y2) Gc_0))
				(and2x3_1 (th22 (rail1 X2) (rail1 Y3) Gc_0))
				(and2x3_0 (th12 (rail0 X2) (rail0 Y3) Gc_0))
				(and2x2_0 (thand0 (rail0 Y2) (rail0 X2) (rail1 Y2) (rail1 X2) Gc_0))
				(and2x2_1 (th22 (rail1 X2) (rail1 Y2) Gc_0))
				(and2x1_1 (th22 (rail1 X2) (rail1 Y1) Gc_0))
				(and2x1_0 (th12 (rail0 X2) (rail0 Y1) Gc_0))
				(and0x1_1 (th22 (rail1 X0) (rail1 Y1) Gc_0))
				(and0x1_0 (th12 (rail0 X0) (rail0 Y1) Gc_0))
				(and0x3_1 (th22 (rail1 X0) (rail1 Y3) Gc_0))
				(and0x3_0 (th12 (rail0 X0) (rail0 Y3) Gc_0))
				(and2x0_0 (th12 (rail0 X2) (rail0 Y0) Gc_0))
				(and3x0_0 (th12 (rail0 X3) (rail0 Y0) Gc_0))
				(and3x2_1 (th22 (rail1 X3) (rail1 Y2) Gc_0))
				(and3x2_0 (th12 (rail0 X3) (rail0 Y2) Gc_0))
				(Z0_1 (th22 (rail1 X0) (rail1 Y0) Gc_0))
				(Z0_0 (thand0 (rail0 Y0) (rail0 X0) (rail1 Y0) (rail1 X0) Gc_0))
				(and3x3_0 (thand0 (rail0 Y3) (rail0 X3) (rail1 Y3) (rail1 X3) Gc_0))
				(and3x3_1 (th22 (rail1 X3) (rail1 Y3) Gc_0))
				(and3x0_1 (th22 (rail1 X3) (rail1 Y0) Gc_0))
				(and2x0_1 (th22 (rail1 X2) (rail1 Y0) Gc_0))
				(and1x0_1 (th22 (rail1 X1) (rail1 Y0) Gc_0))
				(and1x0_0 (th12 (rail0 X1) (rail0 Y0) Gc_0))
				(and3x1_0 (th12 (rail0 X3) (rail0 Y1) Gc_0))
				(and3x1_1 (th22 (rail1 X3) (rail1 Y1) Gc_0))
				(and1x1_0 (thand0 (rail0 Y1) (rail0 X1) (rail1 Y1) (rail1 X1) Gc_0))
				(and1x1_1 (th22 (rail1 X1) (rail1 Y1) Gc_0))
				(and1x2_1 (th22 (rail1 X1) (rail1 Y2) Gc_0))
				(and1x2_0 (th12 (rail0 X1) (rail0 Y2) Gc_0))
				(and1x3_0 (th12 (rail0 X1) (rail0 Y3) Gc_0))
				(and1x3_1 (th22 (rail1 X1) (rail1 Y3) Gc_0))
			)
		(let
			(
				(Z1_1 (th24comp and0x1_0 and1x0_0 and0x1_1 and1x0_1 Gc_0))
				(C1x1_0 (th12 and0x1_0 and1x0_0 Gc_0))
				(C1x1_1 (th22 and0x1_1 and1x0_1 Gc_0))
				(Z1_0 (th24comp and0x1_0 and1x0_1 and1x0_0 and0x1_1 Gc_0))
			)
		(let
			(
				(C1x2_1 (th23 and2x0_1 and1x1_1 C1x1_1 Gc_0))
				(C1x2_0 (th23 and2x0_0 and1x1_0 C1x1_0 Gc_0))
			)
		(let
			(
				(S1x2_1 (th34w2 C1x2_0 and2x0_1 and1x1_1 C1x1_1 Gc_0))
				(C1x3_0 (th23 and3x0_0 and2x1_0 C1x2_0 Gc_0))
				(C1x3_1 (th23 and3x0_1 and2x1_1 C1x2_1 Gc_0))
				(S1x2_0 (th34w2 C1x2_1 and2x0_0 and1x1_0 C1x1_0 Gc_0))
			)
		(let
			(
				(S1x3_0 (th34w2 C1x3_1 and3x0_0 and2x1_0 C1x2_0 Gc_0))
				(S1x3_1 (th34w2 C1x3_0 and3x0_1 and2x1_1 C1x2_1 Gc_0))
				(Z2_1 (th24comp S1x2_0 and0x2_0 S1x2_1 and0x2_1 Gc_0))
				(Z2_0 (th24comp S1x2_0 and0x2_1 and0x2_0 S1x2_1 Gc_0))
				(C2x2_0 (th12 S1x2_0 and0x2_0 Gc_0))
				(C2x2_1 (th22 S1x2_1 and0x2_1 Gc_0))
			)
		(let
			(
				(C2x3_1 (th23 and1x2_1 S1x3_1 C2x2_1 Gc_0))
				(C2x3_0 (th23 and1x2_0 S1x3_0 C2x2_0 Gc_0))
			)
		(let
			(
				(C2x4_0 (th23 and3x1_0 C1x3_0 C2x3_0 Gc_0))
				(C2x4_1 (th23 and3x1_1 C1x3_1 C2x3_1 Gc_0))
				(S2x3_1 (th34w2 C2x3_0 and1x2_1 S1x3_1 C2x2_1 Gc_0))
				(S2x3_0 (th34w2 C2x3_1 and1x2_0 S1x3_0 C2x2_0 Gc_0))
			)
		(let
			(
				(Z3_0 (th24comp S2x3_0 and0x3_1 and0x3_0 S2x3_1 Gc_0))
				(Z3_1 (th24comp S2x3_0 and0x3_0 S2x3_1 and0x3_1 Gc_0))
				(S2x4_0 (th34w2 C2x4_1 and3x1_0 C1x3_0 C2x3_0 Gc_0))
				(S2x4_1 (th34w2 C2x4_0 and3x1_1 C1x3_1 C2x3_1 Gc_0))
				(C3x3_0 (th12 S2x3_0 and0x3_0 Gc_0))
				(C3x3_1 (th22 S2x3_1 and0x3_1 Gc_0))
			)
		(let
			(
				(C3x4_1 (th23 and2x2_1 S2x4_1 C3x3_1 Gc_0))
				(C3x4_0 (th23 and2x2_0 S2x4_0 C3x3_0 Gc_0))
			)
		(let
			(
				(S3x4_1 (th34w2 C3x4_0 and2x2_1 S2x4_1 C3x3_1 Gc_0))
				(S3x4_0 (th34w2 C3x4_1 and2x2_0 S2x4_0 C3x3_0 Gc_0))
				(C3x5_0 (th23 and3x2_0 C2x4_0 C3x4_0 Gc_0))
				(C3x5_1 (th23 and3x2_1 C2x4_1 C3x4_1 Gc_0))
			)
		(let
			(
				(Z4_1 (th24comp S3x4_0 and1x3_0 S3x4_1 and1x3_1 Gc_0))
				(Z4_0 (th24comp S3x4_0 and1x3_1 and1x3_0 S3x4_1 Gc_0))
				(S3x5_0 (th34w2 C3x5_1 and3x2_0 C2x4_0 C3x4_0 Gc_0))
				(S3x5_1 (th34w2 C3x5_0 and3x2_1 C2x4_1 C3x4_1 Gc_0))
				(C4x4_0 (th12 S3x4_0 and1x3_0 Gc_0))
				(C4x4_1 (th22 S3x4_1 and1x3_1 Gc_0))
			)
		(let
			(
				(C4x5_1 (th23 and2x3_1 S3x5_1 C4x4_1 Gc_0))
				(C4x5_0 (th23 and2x3_0 S3x5_0 C4x4_0 Gc_0))
			)
		(let
			(
				(Z7_0 (th23 and3x3_0 C3x5_0 C4x5_0 Gc_0))
				(Z7_1 (th23 and3x3_1 C3x5_1 C4x5_1 Gc_0))
				(Z5_0 (th34w2 C4x5_1 and2x3_0 S3x5_0 C4x4_0 Gc_0))
				(Z5_1 (th34w2 C4x5_0 and2x3_1 S3x5_1 C4x4_1 Gc_0))
			)
		(let
			(
				(Z6_1 (th34w2 Z7_0 and3x3_1 C3x5_1 C4x5_1 Gc_0))
				(Z6_0 (th34w2 Z7_1 and3x3_0 C3x5_0 C4x5_0 Gc_0))
			)
		(let
			(
				(Z0 (concat Z0_1 Z0_0))
				(Z1 (concat Z1_1 Z1_0))
				(Z2 (concat Z2_1 Z2_0))
				(Z3 (concat Z3_1 Z3_0))
				(Z4 (concat Z4_1 Z4_0))
				(Z5 (concat Z5_1 Z5_0))
				(Z6 (concat Z6_1 Z6_0))
				(Z7 (concat Z7_1 Z7_0))
			)
		(let
			(
				(P0 ((_ extract 3 2) (ncl_ha ACC0 Z0 Gc_0)))
				(CA0 ((_ extract 1 0) (ncl_ha ACC0 Z0 Gc_0)))
			)
		(let
			(
				(P1 ((_ extract 3 2) (ncl_fa ACC1 Z1 CA0 Gc_0)))
				(CA1 ((_ extract 1 0) (ncl_fa ACC1 Z1 CA0 Gc_0)))
        	)
		(let
			(
				(P2 ((_ extract 3 2) (ncl_fa ACC2 Z2 CA1 Gc_0)))
				(CA2 ((_ extract 1 0) (ncl_fa ACC2 Z2 CA1 Gc_0)))
			)
		(let
			(
				(P3 ((_ extract 3 2) (ncl_fa ACC3 Z3 CA2 Gc_0)))
				(CA3 ((_ extract 1 0) (ncl_fa ACC3 Z3 CA2 Gc_0)))
			)
		(let
			(
				(P4 ((_ extract 3 2) (ncl_fa ACC4 Z4 CA3 Gc_0)))
				(CA4 ((_ extract 1 0) (ncl_fa ACC4 Z4 CA3 Gc_0)))
			)
		(let
			(
				(P5 ((_ extract 3 2) (ncl_fa ACC5 Z5 CA4 Gc_0)))
				(CA5 ((_ extract 1 0) (ncl_fa ACC5 Z5 CA4 Gc_0)))
			)
		(let
			(
				(P6 ((_ extract 3 2) (ncl_fa ACC6 Z6 CA5 Gc_0)))
				(P7 ((_ extract 1 0) (ncl_fa ACC6 Z6 CA5 Gc_0)))
			)
		(let
			(
				(acc0_1 (Reg_DATA0 P0 Ki1 reset cs1))
				(acc1_1 (Reg_DATA0 P1 Ki1 reset cs1))
				(acc2_1 (Reg_DATA0 P2 Ki1 reset cs1))
				(acc3_1 (Reg_DATA0 P3 Ki1 reset cs1))
				(acc4_1 (Reg_DATA0 P4 Ki1 reset cs1))
				(acc5_1 (Reg_DATA0 P5 Ki1 reset cs1))
				(acc6_1 (Reg_DATA0 P6 Ki1 reset cs1))
				(acc7_1 (Reg_DATA0 P7 Ki1 reset cs1))
			)
		(let
			(
				(and1x2_sync (bvand (rail1 X1) (rail1 Y2)))
				(and1x3_sync (bvand (rail1 X1) (rail1 Y3)))
				(and1x0_sync (bvand (rail1 X1) (rail1 Y0)))
				(and1x1_sync (bvand (rail1 X1) (rail1 Y1)))
				(and2x1_sync (bvand (rail1 X2) (rail1 Y1)))
				(and0x3_sync (bvand (rail1 X0) (rail1 Y3)))
				(and0x2_sync (bvand (rail1 X0) (rail1 Y2)))
				(and0x1_sync (bvand (rail1 X0) (rail1 Y1)))
				(and2x0_sync (bvand (rail1 X2) (rail1 Y0)))
				(and3x0_sync (bvand (rail1 X3) (rail1 Y0)))
				(and2x3_sync (bvand (rail1 X2) (rail1 Y3)))
				(and3x2_sync (bvand (rail1 X3) (rail1 Y2)))
				(and3x3_sync (bvand (rail1 X3) (rail1 Y3)))
				(and2x2_sync (bvand (rail1 X2) (rail1 Y2)))
				(Z0_sync (bvand (rail1 X0) (rail1 Y0)))
				(and3x1_sync (bvand (rail1 X3) (rail1 Y1)))
			)
		(let
			(
				(C1x1_sync (bvand and1x0_sync and0x1_sync))
				(I0_sync (bvxor and2x0_sync and1x1_sync))
				(I3_sync (bvxor and3x0_sync and2x1_sync))
				(I2_sync (bvand and2x0_sync and1x1_sync))
				(I5_sync (bvand and3x0_sync and2x1_sync))
				(Z1_sync (bvxor and1x0_sync and0x1_sync))
			)
		(let
			(
				(I1_sync (bvand I0_sync C1x1_sync))
				(S1x2_sync (bvxor I0_sync C1x1_sync))
			)
		(let
			(
				(C1x2_sync (bvor I1_sync I2_sync))
				(Z2_sync (bvxor and0x2_sync S1x2_sync))
				(C2x2_sync (bvand and0x2_sync S1x2_sync))
			)
		(let
			(
				(I4_sync (bvand I3_sync C1x2_sync))
				(S1x3_sync (bvxor I3_sync C1x2_sync))
			)
		(let
			(
				(I8_sync (bvand and1x2_sync S1x3_sync))
				(C1x3_sync (bvor I4_sync I5_sync))
				(I6_sync (bvxor and1x2_sync S1x3_sync))
			)
		(let
			(
				(I9_sync (bvxor and3x1_sync C1x3_sync))
				(S2x3_sync (bvxor I6_sync C2x2_sync))
				(I11_sync (bvand and3x1_sync C1x3_sync))
				(I7_sync (bvand I6_sync C2x2_sync))
			)
		(let
			(
				(C2x3_sync (bvor I7_sync I8_sync))
				(C3x3_sync (bvand and0x3_sync S2x3_sync))
				(Z3_sync (bvxor and0x3_sync S2x3_sync))
			)
		(let
			(
				(S2x4_sync (bvxor I9_sync C2x3_sync))
				(I10_sync (bvand I9_sync C2x3_sync))
			)
		(let
			(
				(I14_sync (bvand and2x2_sync S2x4_sync))
				(C2x4_sync (bvor I10_sync I11_sync))
				(I12_sync (bvxor and2x2_sync S2x4_sync))
			)
		(let
			(
				(I15_sync (bvxor and3x2_sync C2x4_sync))
				(S3x4_sync (bvxor I12_sync C3x3_sync))
				(I17_sync (bvand and3x2_sync C2x4_sync))
				(I13_sync (bvand I12_sync C3x3_sync))
			)
		(let
			(
				(Z4_sync (bvxor and1x3_sync S3x4_sync))
				(C3x4_sync (bvor I13_sync I14_sync))
				(C4x4_sync (bvand and1x3_sync S3x4_sync))
			)
		(let
			(
				(I16_sync (bvand I15_sync C3x4_sync))
				(S3x5_sync (bvxor I15_sync C3x4_sync))
			)
		(let
			(
				(I20_sync (bvand and2x3_sync S3x5_sync))
				(C3x5_sync (bvor I16_sync I17_sync))
				(I18_sync (bvxor and2x3_sync S3x5_sync))
			)
		(let
			(
				(I21_sync (bvxor and3x3_sync C3x5_sync))
				(I23_sync (bvand and3x3_sync C3x5_sync))
				(I19_sync (bvand I18_sync C4x4_sync))
				(Z5_sync (bvxor I18_sync C4x4_sync))
			)
		(let
			(
				(C4x5_sync (bvor I19_sync I20_sync))
			)
		(let
			(
				(I22_sync (bvand I21_sync C4x5_sync))
				(Z6_sync (bvxor I21_sync C4x5_sync))
			)
		(let
			(
				(Z7_sync (bvor I22_sync I23_sync))
			)
		(let
			(
				(P0_sync (sync_HA_sum (rail1 ACC0) Z0_sync))
				(C0_sync (sync_HA_carry (rail1 ACC0) Z0_sync))
			)
		(let
			(
				(P1_sync (sync_FA_sum C0_sync (rail1 ACC1) Z1_sync))
				(C1_sync (sync_FA_carry C0_sync (rail1 ACC1) Z1_sync))
			)
		(let
			(
				(P2_sync (sync_FA_sum C1_sync (rail1 ACC2) Z2_sync))
				(C2_sync (sync_FA_carry C1_sync (rail1 ACC2) Z2_sync))
			)
		(let
			(
				(P3_sync (sync_FA_sum C2_sync (rail1 ACC3) Z3_sync))
				(C3_sync (sync_FA_carry C2_sync (rail1 ACC3) Z3_sync))
			)
		(let
			(
				(P4_sync (sync_FA_sum C3_sync (rail1 ACC4) Z4_sync))
				(C4_sync (sync_FA_carry C3_sync (rail1 ACC4) Z4_sync))
			)
		(let
			(
				(P5_sync (sync_FA_sum C4_sync (rail1 ACC5) Z5_sync))
				(C5_sync (sync_FA_carry C4_sync (rail1 ACC5) Z5_sync))
			)
		(let
			(
				(P6_sync (sync_FA_sum C5_sync (rail1 ACC6) Z6_sync))
				(P7_sync (sync_FA_carry C5_sync (rail1 ACC6) Z6_sync))
			)
		(let
			(
				(acc0_1_sync (sync_Reg0 P0_sync Ki1 reset (rail1 cs1)))
				(acc1_1_sync (sync_Reg0 P1_sync Ki1 reset (rail1 cs1)))
				(acc2_1_sync (sync_Reg0 P2_sync Ki1 reset (rail1 cs1)))
				(acc3_1_sync (sync_Reg0 P3_sync Ki1 reset (rail1 cs1)))
				(acc4_1_sync (sync_Reg0 P4_sync Ki1 reset (rail1 cs1)))
				(acc5_1_sync (sync_Reg0 P5_sync Ki1 reset (rail1 cs1)))
				(acc6_1_sync (sync_Reg0 P6_sync Ki1 reset (rail1 cs1)))
				(acc7_1_sync (sync_Reg0 P7_sync Ki1 reset (rail1 cs1)))
			)
		(=>
			(and
				(= (_ bv0 1) Gc_0)
				(= (_ bv1 1) Ki0)
				(= (_ bv1 1) Ki1)
				(datap Xi0)
				(datap Xi1)
				(datap Xi2)
				(datap Xi3)
				(datap Yi0)
				(datap Yi1)
				(datap Yi2)
				(datap Yi3)
				(datap acci0)
				(datap acci1)
				(datap acci2)
				(datap acci3)
				(datap acci4)
				(datap acci5)
				(datap acci6)
				(datap acci7)
				(= o_ncl (concat (rail1 acc7_1) (rail1 acc6_1) (rail1 acc5_1) (rail1 acc4_1) (rail1 acc3_1) (rail1 acc2_1) (rail1 acc1_1) (rail1 acc0_1)))
				(= o_sync (concat acc7_1_sync acc6_1_sync acc5_1_sync acc4_1_sync acc3_1_sync acc2_1_sync acc1_1_sync acc0_1_sync))
				(= i_x (concat (rail1 Xi3) (rail1 Xi2) (rail1 Xi1) (rail1 Xi0)))
				(= i_y (concat (rail1 Yi3) (rail1 Yi2) (rail1 Yi1) (rail1 Yi0)))
				(= i_acc (concat (rail1 acci7) (rail1 acci6) (rail1 acci5) (rail1 acci4) (rail1 acci3) (rail1 acci2) (rail1 acci1) (rail1 acci0)))
				(= o_z (concat Z7_1 Z6_1 Z5_1 Z4_1 Z3_1 Z2_1 Z1_1 Z0_1))
			)
			(and
				(= (rail1 acc0_1) acc0_1_sync)
				(= (rail1 acc1_1) acc1_1_sync)
				(= (rail1 acc2_1) acc2_1_sync)
				(= (rail1 acc3_1) acc3_1_sync)
				(= (rail1 acc4_1) acc4_1_sync)
				(= (rail1 acc5_1) acc5_1_sync)
				(= (rail1 acc6_1) acc6_1_sync)
				(= (rail1 acc7_1) acc7_1_sync)
			)
		)))))))))))))))))))))))))))))))))))))))))))))))))))
	)
)

(check-sat)
(get-model)
