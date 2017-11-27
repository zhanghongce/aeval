(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var z Int)

(declare-rel fail ())

(rule (=> (and (> y 0) (<= z 0)) (inv x y z)))

(rule (=> 
    (and 
        (inv x y z)
        (> x 0)
        (or (= x1 (- x y)) (= x1 (+ x z)))
    )
    (inv x1 y z)
  )
)

(rule (=> (and (inv x y z) (> x 0)) fail))

(query fail :print-certificate true)
