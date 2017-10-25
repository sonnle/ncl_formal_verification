; NCL Gate Boolean Function - TH34w32: (A + BC + BD)
(define-fun th34w32 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
                (bvor a
                	(bvand b c)
                	(bvand b d)))
            (_ bv1 1)
            g_l))
)
