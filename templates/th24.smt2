; NCL Gate Boolean Function - TH24: (AB + AC + AD + BC + BD + CD)
(define-fun th24 ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (d (_ BitVec 1)) (gl (_ BitVec 1))) (_ BitVec 1)
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
                	(bvand a b)
                	(bvand a c)
                	(bvand a d)
                	(bvand b c)
                	(bvand b d)
                	(bvand c d)))
            (_ bv1 1)
            gl))
)
