(declare-rel inv (Int ))
(declare-var x Int)
(declare-var x1 Int)

(rule (inv x))

(rule (=> 
    (and 
        (inv x)
        (> x 5)
        (= x1 (ite (= x 10) x (- x 1)))
    )
    (inv x1)
  )
)
