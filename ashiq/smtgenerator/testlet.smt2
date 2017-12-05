; Formal verification proof of input completeness of NCL circuit
(set-logic QF_BV)

; Inputs
(declare-fun a () (_ BitVec 1))
(declare-fun b () (_ BitVec 1))
(declare-fun c () (_ BitVec 1))
(declare-fun m () (_ BitVec 1))

(declare-fun a1 () (_ BitVec 1))
(declare-fun b1 () (_ BitVec 1))
(declare-fun c1 () (_ BitVec 1))
(declare-fun m1 () (_ BitVec 1))

; Outputs
(declare-fun out_pchb () (_ BitVec 1))
(declare-fun out_sync () (_ BitVec 1))

(declare-fun d () (_ BitVec 1))
(declare-fun f () (_ BitVec 1))

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
        (=>
			(and
				(= a a1)
				(= b b1)
				(= c c1)
				(= m m1))
				
            (= out_pchb out_sync ) ) ) ) ) ) )
)

(check-sat)
(get-model)
(get-value (a))
(get-value (b))
(get-value (c))
(get-value (m))
(get-value (d))
(get-value (f))
(get-value (out_pchb))

(get-value (a1))
(get-value (b1))
(get-value (c1))
(get-value (m1))
(get-value (out_sync))