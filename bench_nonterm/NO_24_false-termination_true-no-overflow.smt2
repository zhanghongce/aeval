(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv 1 2))

(rule (=> 
    (and 
        (inv x y)
        (< (+ x y) 5)
        (= x1 (- x y))
        (= y1 (+ x1 y))
        (= x2 (- y1 x1))
    )
    (inv x2 y1)
  )
)
