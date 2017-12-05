(declare-rel inv (Int ))
(declare-var x Int)
(declare-var x1 Int)

(rule (inv x))

(rule (=> 
    (and 
        (inv x)
        (not (= x 0))
        (= x1 (ite (and (<= -5 x) (<= x 35)) (ite (< x 0) -5 (ite (> x 30) 35 (- x 1))) 0))
    )
    (inv x1)
  )
)
