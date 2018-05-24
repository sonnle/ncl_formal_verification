; NCL Gate Dual Rail AND Logic
(define-fun and2_relax_buggy_th22 ((a (_ BitVec 2)) (b (_ BitVec 2)) (gl_1 (_ BitVec 1)) (gl_0 (_ BitVec 1))) (_ BitVec 2)
    (concat (bvand (rail1 a) (rail1 b)) (thand0 (rail0 b) (rail0 a) (rail1 b) (rail1 a) gl_0))
)
