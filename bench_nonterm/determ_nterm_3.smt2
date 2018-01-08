(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var x1 Int)
(declare-var y1 Int)

(rule (inv -1 2 3))

(rule (=> 
    (and 
        (inv x y z)
        (not (= x 1))
        (= x1 (+ x z))
        (= z1 (+ y z))
        (= y1 (+ y 2))
    )
    (inv x1 y1 z1)
  )
)
