; NCL Gate Dual Rail Input-Complete AND Logic
(define-fun and2 ((a (_ BitVec 2)) (b (_ BitVec 2)) (gl_1 (_ BitVec 1)) (gl_0 (_ BitVec 1))) (_ BitVec 2)
    (concat (th22 (rail1 a) (rail1 b) gl_1) (thand0 (rail0 b) (rail0 a) (rail1 b) (rail1 a) gl_0))
)
