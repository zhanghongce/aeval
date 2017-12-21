(declare-rel inv ( Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (< x y)
        (= x1 (+ x y))
        (= y1 (* -2 y))
    )
    (inv x1 y1)
  )
)
