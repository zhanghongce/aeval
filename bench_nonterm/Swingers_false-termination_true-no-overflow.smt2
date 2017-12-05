(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(rule (inv 13 17))

(rule (=> 
    (and 
        (inv x y )
        (< (+ x y) 100)
        (= x1 y)
        (= y1 x)
    )
    (inv x1 y1)
  )
)
