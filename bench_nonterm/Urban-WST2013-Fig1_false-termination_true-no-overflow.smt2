(declare-rel inv ( Int ))
(declare-var x Int)
(declare-var x1 Int)

(rule (inv x))

(rule (=> 
    (and 
        (inv x)
        (<= x 10)
        (= x1 (ite (> x 6) (+ x 2) x))
    )
    (inv x1)
  )
)
