(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (=> (= y (+ (* 7 x) 19)) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (> y 0)
        (or (and (= y1 (+ y (* 24 x) 7)) (= x1 x))
            (and (= y1 y) (= x1 (- x 1)))
        )
    )
    (inv x1 y1)
  )
)
