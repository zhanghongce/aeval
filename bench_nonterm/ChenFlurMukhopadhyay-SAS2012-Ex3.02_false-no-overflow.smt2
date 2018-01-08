(declare-rel inv ( Int Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)

(rule (inv x y z))

(rule (=> 
    (and 
        (inv x y z)
        (> x 0)
        (= x1 (+ x y))
        (= y1 (+ y z))
    )
    (inv x1 y1 z)
  )
)
