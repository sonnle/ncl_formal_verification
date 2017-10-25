; NCL Gate Boolean Function - TH34: (ABC + ABD + ACD + BCD)
(define-fun th34 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
                	(bvand a c d)
                	(bvand b c d)))
            (_ bv1 1)
            g_l))
)
