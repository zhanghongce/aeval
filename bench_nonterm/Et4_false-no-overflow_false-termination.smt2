(declare-rel inv (Int Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var r Int)
(declare-var r1 Int)
(rule 
	(inv x y z)
)

(rule (=> 
    (and 
        (inv x y z )
        (>= (- y z) 1)
        (= x z)
        (= y1 10)
        (= z1 (+ z1 1 r) )
        (= x1 z1)
    )
    (inv x1 y1 z1 )
  )
)


