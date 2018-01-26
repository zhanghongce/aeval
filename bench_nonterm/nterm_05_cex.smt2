(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)

(rule (inv x y z))

(rule (=> 
    (and 
        (inv x y z)
        (or (= x z) (= y z))
        (not (= x y))
        (or (and (= x1 (+ x 1)) (= y1 y))
            (and (= x1 x) (= y1 (+ y 1))))
    )
    (inv x1 y1 z)
  )
)
