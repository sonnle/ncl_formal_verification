; NCL Gate Boolean Function - TH24w2: (A + BC + BD + CD)
(define-fun th24w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
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
                	(bvand b d)
                	(bvand c d)))
            (_ bv1 1)
            g_l))
)
