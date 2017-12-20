(set-logic QF_BV)

; Inputs: n01, n02, n03, n06, n07
(declare-fun n01 () (_ BitVec 1))
(declare-fun n02 () (_ BitVec 1))
(declare-fun n03 () (_ BitVec 1))
(declare-fun n06 () (_ BitVec 1))
(declare-fun n07 () (_ BitVec 1))

; Outputs: n22, n23
(declare-fun n22 () (_ BitVec 1))
(declare-fun n23 () (_ BitVec 1))

; SAT/UNSAT assertion for test_netlistc17.txt
(assert
	(not		
		(let
			(
				(n09 (bvnand n01 n03))
				(n08 (bvnand n03 n06))
			)		
		(let
			(
				(n10 (bvnand n02 n08))
				(n11 (bvnand n08 n07))
			)		
		(let
			(
				(n22 (bvnand n09 n10))
				(n23 (bvnand n10 n11))
			)
		(let 
			(
				(out_sync1 (bvnand (bvnand n01 n03) (bvnand (bvnand n03 n06) n02)))
				(out_sync2 (bvnand (bvnand (bvnand n03 n06) n02) (bvnand (bvnand n03 n06) n07) ))
			)
		(and (= n22 out_sync1) (= n23 out_sync2) )))))
	)	
)
(check-sat)
(get-model)