(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)

(declare-rel fail ())

(rule (=> (>= x (* 2 y)) (inv x y)))

(rule (=> 
    (and 
        (inv x y)
        (not (= x (* 2 y)))
        (= x1 (ite (= (mod x y) 1) (+ x 1) (- x 2)))
    )
    (inv x1 y)
  )
)

(rule (=> (and (inv x y) (not (= x (* 2 y)))) fail))

(query fail :print-certificate true)
