(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv 11 17))

(rule (=> 
    (and 
        (inv x y)
        (not (= x y))
        (= x1 (+ y 1))
        (= y1 (+ x 1))
    )
    (inv x1 y1)
  )
)
