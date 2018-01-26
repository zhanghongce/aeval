(declare-rel itp (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var n Int)
(declare-var m Int)
(declare-var n1 Int)

(rule (=> (and (> n 0) (= x 0)) (itp x m n)))

(rule (=> 
    (and 
        (itp x m n)
        (< x n)
        (= x1 (ite (= m 1) (+ x 1) x))
        (= n1 (ite (= m 0) (- n 1) n))
    )
    (itp x1 m n1)
  )
)
