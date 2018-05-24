; NCL Gate Dual Rail AND Logic
(define-fun and2_relax_buggy_thand0 ((a (_ BitVec 2)) (b (_ BitVec 2)) (gl_1 (_ BitVec 1)) (gl_0 (_ BitVec 1))) (_ BitVec 2)
    (concat (th22 (rail1 a) (rail1 b) gl_1) (bvor (bvand (rail0 b) (rail0 a)) (bvand (rail0 a) (rail1 b)) (bvand (rail0 b) (rail1 a))))
)
