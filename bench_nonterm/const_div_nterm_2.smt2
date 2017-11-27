(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)

(declare-rel fail ())

(rule (inv x y))

(rule (=> 
    (and 
        (inv x y)
        (= (div x 50) y)
        (= x1 (+ x (* 50 z)))
        (= y1 (+ y z))
    )
    (inv x1 y1)
  )
)

(rule (=> (and (inv x y) (= (div x 50) y)) fail))

(query fail :print-certificate true)
