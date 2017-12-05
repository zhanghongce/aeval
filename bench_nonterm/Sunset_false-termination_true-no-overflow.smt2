(declare-rel inv (Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)

(rule (inv x))

(rule (=> 
    (and 
        (inv x)
        (> x 10)
        (= x1 (ite (= x 25) 30 x))
        (= x2 (ite (<= x1 30) (- x1 1) 20))
    )
    (inv x2)
  )
)
