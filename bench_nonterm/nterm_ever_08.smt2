(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (not (= x 10))
        (not (= y 12))
        (= x1 (ite (= (mod x 5) 1) (- x 2) (- x 1)))
        (= y1 (ite (= (mod y 6) 1) (- y 2) (- y 1)))
    )
    (inv x1 y1)
  )
)
