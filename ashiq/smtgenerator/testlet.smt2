; Formal verification proof of input completeness of NCL circuit
(set-logic QF_BV)

; Inputs
(declare-fun a () (_ BitVec 1))
(declare-fun b () (_ BitVec 1))
(declare-fun c () (_ BitVec 1))
(declare-fun m () (_ BitVec 1))

; Outputs
(declare-fun out_pchb () (_ BitVec 1))
(declare-fun out_sync () (_ BitVec 1))

(assert
    (not
        (let
            (
                (d (bvand a b))
			)
        (let 
			(
				(f (bvor d c))
			)
        (let
			(
			(out_pchb (bvxor f m))
            )
        (let
            (
                (out_sync (bvxor m1 (bvor c1 (bvand a1 b1)) ) ) 
                
            )
				
            (= out_pchb out_sync ) ) ) ) ) 
	)	
)


(check-sat)
(get-model)
