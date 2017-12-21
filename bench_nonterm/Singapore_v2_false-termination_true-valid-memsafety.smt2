(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (=> (and (<= -65535 x) (<= x 65535) (<= -65535 y) (<= y 65535) (> (+ x y) 1)) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (> x 0)
        (= x1 (+ x x y))
        (= y1 (- y 1))
    )
    (inv x1 y1)
  )
)
