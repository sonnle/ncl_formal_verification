; NCL Half-Adder
; The output will be concatenated as follows:        | variable - S1, S0, Cout1, Cout0
;                                                    |      bit -  3,  2,     1,     0
; The last gate values (gl) will be used as follows: | variable -      gl_3,      gl_2, gl_1, gl_0
;                                                    |     gate - th24comp0, th24comp1, th12, th22
(define-fun ha ((x (_ BitVec 2)) (y (_ BitVec 2)) (gl_3 (_ BitVec 1)) (gl_2 (_ BitVec 1)) (gl_1 (_ BitVec 1)) (gl_0 (_ BitVec 1))) (_ BitVec 4)
    (concat
        (th24comp (rail0 y) (rail0 x) (rail1 y) (rail1 x) gl_3)
        (th24comp (rail0 y) (rail1 x) (rail0 x) (rail1 y) gl_2)
        (th22 (rail1 y) (rail1 x) gl_1)
        (th12 (rail0 y) (rail0 x) gl_0))
)
