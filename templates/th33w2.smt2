; NCL Gate Boolean Function - TH33w2: (AB + AC)
(define-fun th33w2 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (g_l (_ BitVec 1))) (_ BitVec 1)
    (ite
        (=
            (_ bv1 1)
            (bvand
                (bvnot a)
                (bvnot b)
                (bvnot c)))
        (_ bv0 1)
        (ite
            (=
                (_ bv1 1)
                (bvor
                	(bvand a b)
                	(bvand a c)))
            (_ bv1 1)
            g_l))
)
