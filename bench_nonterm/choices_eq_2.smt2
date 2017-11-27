(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-rel fail ())

(rule (inv x y ))

(rule (=> 
    (and 
        (inv x y)
        (not (= x y))
        (or (and (= x1 (- x 1)) (= y1 (+ y 1)))
            (and (= x1 (+ x 1)) (= y1 (- y 1))))
    )
    (inv x1 y1 )
  )
)

(rule (=> (and (inv x y ) (not (= x y))) fail))

(query fail :print-certificate true)
