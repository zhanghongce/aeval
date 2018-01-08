(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)

(rule (=> (> y 0) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (= x 10000000)
        (= x1 (* x y))
    )
    (inv x1 y)
  )
)
