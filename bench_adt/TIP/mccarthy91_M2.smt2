(declare-fun m (Int) Int)
(assert
  (not (forall ((n Int)) (=> (>= n 101) (= (m n) (- n 10))))))
(assert
  (forall ((x Int))
    (= (m x) (ite (> x 100) (- x 10) (m (m (+ x 11)))))))
(check-sat)
