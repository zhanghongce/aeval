(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var c Int)
(declare-var c1 Int)

(rule (inv c x))

(rule (=> 
    (and 
        (inv c x)
        (> c 0)
        (= c1 (ite (> x 100) (- c 1) (+ c 1)))
        (= x1 (ite (> x 100) (- x 10) (+ x 11)))
    )
    (inv c1 x1)
  )
)
