(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (= x (* 3 y))
        (= y1 (+ x y))
        (or (= x1 (* 4 x)) (= x1 (+ y1 1)))
    )
    (inv x1 y1)
  )
)
