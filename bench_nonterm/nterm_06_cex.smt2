(declare-rel inv (Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (inv 0 0))

(rule (=> 
    (and 
        (inv x y)
        (= x y)
        (= x1 (+ x 1))
    )
    (inv x1 y1)
  )
)

(rule (=> (and (inv x y) (= x y)) fail))

(query fail :print-certificate true)
