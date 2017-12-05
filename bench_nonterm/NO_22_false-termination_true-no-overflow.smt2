(declare-rel inv (Int ))
(declare-var x Int)
(declare-var x1 Int)

(rule (inv 0))

(rule (=> 
    (and 
        (inv x)
        (< x 100)
        (= x1 (ite (< x 50) (+ x 1) (- x 1)))
    )
    (inv x1)
  )
)
