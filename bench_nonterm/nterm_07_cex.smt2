(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)

(declare-rel fail ())

(rule (=> (> x y) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (not (= x y))
        (= x1 (- x 3))
        (= y1 (- y 1))
    )
    (inv x1 y1)
  )
)

(rule (=> (and (inv x y) (not (= x y))) fail))

(query fail :print-certificate true)
