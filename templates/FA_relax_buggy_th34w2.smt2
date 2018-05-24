; NCL Full-Adder
; The output will be concatenated as follows:        | variable - S1, S0, Cout1, Cout0
;                                                    |      bit -  3,  2,     1,     0
; The last gate values (gl) will be used as follows: | variable -        gl_3,        gl_2,         gl_1,         gl_0
;                                                    |     gate - th23 rail 0, th23 rail 1, th35w2 rail0, th35w2 rail1
(define-fun fa_relax_buggy_th34w2 ((x (_ BitVec 2)) (y (_ BitVec 2)) (cin (_ BitVec 2)) (gl_3 (_ BitVec 1)) (gl_2 (_ BitVec 1)) (gl_1 (_ BitVec 1)) (gl_0 (_ BitVec 1))) (_ BitVec 4)
    (let
        (
            (gn_0 (th23 (rail0 x) (rail0 y) (rail0 cin) gl_0))
            (gn_1 (th23 (rail1 x) (rail1 y) (rail1 cin) gl_1))
        )
    (let
        (
            (gn_2 (bvor (bvand gn_1 (rail0 x)) (bvand gn_1 (rail0 y)) (bvand gn_1 (rail0 cin)) (bvand (rail0 x) (rail0 y) (rail0 cin))))
            (gn_3 (bvor (bvand gn_0 (rail1 x)) (bvand gn_0 (rail1 y)) (bvand gn_0 (rail1 cin)) (bvand (rail1 x) (rail1 y) (rail1 cin))))
        )
    (concat gn_3 gn_2 gn_1 gn_0)))
)
