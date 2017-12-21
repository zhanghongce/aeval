(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (inv 0 1))

(rule (=> 
    (and 
        (inv x y)
        (< x 6)
        (= x1 (+ x 1))
        (= y1 (* y 2))
    )
    (inv x1 y1)
  )
)
