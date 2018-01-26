(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (or (and (> x 0) (> y 0)) (and (< x 0) (< y 0)))
        (= y1 (* -7 y))
        (= x1 (* -9 x))
    )
    (inv x1 y1)
  )
)