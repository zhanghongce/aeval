(declare-rel inv (Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)

(rule (inv 0))

(rule (=> 
    (and 
        (inv x)
        (not (= x 6))
        (or (= y 1) (= y 2) (= y 4) (= y 5))
        (= x1 (+ x y))
    )
    (inv x1)
  )
)
