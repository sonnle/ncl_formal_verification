; Formal verification proof - input completeness of test_netlist4x16.txt
(set-logic QF_BV)

; Inputs: s0, s1, s2, s3
(declare-fun s0 () (_ BitVec 1))
(declare-fun s1 () (_ BitVec 1))
(declare-fun s2 () (_ BitVec 1))
(declare-fun s3 () (_ BitVec 1))

; Outputs: p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15
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
(declare-fun p12 () (_ BitVec 1))
(declare-fun p13 () (_ BitVec 1))
(declare-fun p14 () (_ BitVec 1))
(declare-fun p15 () (_ BitVec 1))

; SAT/UNSAT assertion for test_netlist4x16.txt
(assert
	(not		
		(let
			(
				(s0bar (bvnot s0))
				(s1bar (bvnot s1))
				(s2bar (bvnot s2))
				(s3bar (bvnot s3))
			)		
		(let
			(
				(p0 (bvand s0bar s1bar s2bar s3bar))
				(p1 (bvand s0bar s1bar s2bar s3))
				(p2 (bvand s0bar s1bar s2 s3bar))
				(p3 (bvand s0bar s1bar s2 s3))
				(p4 (bvand s0bar s1 s2bar s3bar))
				(p5 (bvand s0bar s1 s2bar s3))
				(p6 (bvand s0bar s1 s2 s3bar))
				(p7 (bvand s0bar s1 s2 s3))
				(p8 (bvand s0 s1bar s2bar s3bar))
				(p9 (bvand s0 s1bar s2bar s3))
				(p10 (bvand s0 s1bar s2 s3bar))
				(p11 (bvand s0 s1bar s2 s3))
				(p12 (bvand s0 s1 s2bar s3bar))
				(p13 (bvand s0 s1 s2bar s3))
				(p14 (bvand s0 s1 s2 s3bar))
				(p15 (bvand s0 s1 s2 s3))
			)
		(let 
			(
			( s_t (concat s0 s1 s2 s3))
			( out_pchb (concat p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0))
			)
		(let 
			(
			(out_sync (ite (= s_t (_ bv0 4)) (_ bv1 16)
					  (ite (= s_t (_ bv1 4)) (_ bv2 16)
					  (ite (= s_t (_ bv2 4)) (_ bv4 16)
					  (ite (= s_t (_ bv3 4)) (_ bv8 16)
					  (ite (= s_t (_ bv4 4)) (_ bv16 16)
					  (ite (= s_t (_ bv5 4)) (_ bv32 16)
					  (ite (= s_t (_ bv6 4)) (_ bv64 16)
					  (ite (= s_t (_ bv7 4)) (_ bv128 16)
					  (ite (= s_t (_ bv8 4)) (_ bv256 16)
					  (ite (= s_t (_ bv9 4)) (_ bv512 16)
					  (ite (= s_t (_ bv10 4)) (_ bv1024 16)
					  (ite (= s_t (_ bv11 4)) (_ bv2048 16)
					  (ite (= s_t (_ bv12 4)) (_ bv4096 16)
					  (ite (= s_t (_ bv13 4)) (_ bv8192 16)
					  (ite (= s_t (_ bv14 4)) (_ bv16384 16) (_ bv32768 16) ))))))))))))))) )
			)
		(= out_pchb out_sync) )) ))
	)	
)
(check-sat)
(get-model)
