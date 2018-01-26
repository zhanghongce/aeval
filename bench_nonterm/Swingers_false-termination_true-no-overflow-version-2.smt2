(declare-rel inv (Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var w Int)

(rule (inv 11 17 21 25))

(rule (=> 
    (and 
        (inv x y z w)
        (not (= (+ x y) (+ z w)))
        (= x1 z)
        (= z1 x)
    )
    (inv x1 y z1 w)
  )
)
