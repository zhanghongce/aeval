(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)

(rule (inv x y ))

(rule (=> 
    (and 
        (inv x y )
        (> x 0)
        (> y 0)
        (= x1 (+ (* 10 y) (* -2 x)))
    )
    (inv x1 y )
  )
)
