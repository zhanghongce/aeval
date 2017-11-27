(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (= x 0) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (< x 100)
        (= x1 (+ x y))
        (= y1 (- y 1))
    )
    (inv x1 y1)
  )
)

(rule (=> (and (inv x y) (< x 100)) fail))

(query fail :print-certificate true)
