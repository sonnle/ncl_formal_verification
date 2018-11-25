; NCL Gate Dual Rail RegN Logic
(define-fun regN ((a (_ BitVec 2)) (reset (_ BitVec 1)) (ki (_ BitVec 1)) (a_cur (_ BitVec 2))) (_ BitVec 3)
    (ite
        (= (_ bv1 1) reset)
        (concat (_ bv0 2) (_ bv1 1))
        (ite
            (and (= (_ bv1 1) ki) (datap a))
            (concat a (_ bv0 1))
            (ite
                (datap a_cur)
                (concat a_cur (_ bv0 1))
                (concat a_cur (_ bv1 1)))))
)
