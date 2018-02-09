; NCL Gate Boolean Function - TH44w2: (ABC + ABD + ACD)
(define-fun th44w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
    (ite
        (=
            (_ bv1 1)
            (bvand
                (bvnot a)
                (bvnot b)
                (bvnot c)
                (bvnot d)))
        (_ bv0 1)
        (ite
            (=
                (_ bv1 1)
                (bvor 
                	(bvand a b c)
                	(bvand a b d)
                	(bvand a c d)))
            (_ bv1 1)
            gl))
)
