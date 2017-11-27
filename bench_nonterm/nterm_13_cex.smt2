(declare-rel inv (Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)

(declare-rel fail ())

(rule (=> (and (>= x 0) (> y 1)) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (> x 0)
        (or (= x1 (mod x 2)) (= x1 (- x y)))
    )
    (inv x1 y)
  )
)

(rule (=> (and (inv x y) (> x 0)) fail))

(query fail :print-certificate true)
