; NCL Gate Dual Rail AND Logic
(define-fun and2_incomplete_relax ((a (_ BitVec 2)) (b (_ BitVec 2)) (gl_1 (_ BitVec 1)) (gl_0 (_ BitVec 1))) (_ BitVec 2)
    (concat (bvand (rail1 a) (rail1 b)) (th12 (rail0 a) (rail0 b) gl_0))
)
