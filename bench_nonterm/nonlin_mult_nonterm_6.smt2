(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(rule (inv x y z))

(rule (=> 
    (and 
        (inv x y z)
        (= (* x y z) 0)
        (or (and (= x1 0) (= y1 y) (= z1 z))
            (and (= x1 x) (= y1 0) (= z1 z))
            (and (= x1 x) (= y1 y) (= z1 0)))
    )
    (inv x1 y1 z1)
  )
)
