(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var b Bool)

(rule (inv 0 0 z))

(rule (=> 
    (and 
        (inv x y z)
        (< x z)
        (= b (= x y))
        (= x1 (ite b 0 (+ x 1)))
        (= y1 (ite b (+ y 1) y))
        (= z1 (ite b (+ y1 1) z))
    )
    (inv x1 y1 z1)
  )
)
