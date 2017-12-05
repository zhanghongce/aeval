(declare-rel inv ( Int ))
(declare-var x Int)
(declare-var x1 Int)

(rule (inv x))

(rule (=> 
    (and 
        (inv x)
        (not (= x 0))
        (= x1 (ite (and (> x -5) (< x 5)) (ite (< x 0) (+ x 1) x) (ite (> x 0) (- x 1) x)))
    )
    (inv x1)
  )
)
