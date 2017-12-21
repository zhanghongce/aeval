(declare-rel inv (Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var res Int)
(declare-var res1 Int)

(rule (inv x y y 0))

(rule (=> 
    (and 
        (inv x y z res)
        (> z 0)
        (or (= y 0) (and (> y 0) (> x 0)))
        (= x1 (ite (= y 0) x (+ x 1)))
        (= y1 (ite (= y 0) z (- y 1)))
        (= res1 (ite (= y 0) (+ res 1) res))
    )
    (inv x1 y1 z res1)
  )
)
