(declare-rel inv (Int))
(declare-var j Int)
(declare-var j1 Int)

(rule (inv j))

(rule (=> 
    (and 
        (inv j)
        (>= j 1)
        (= j1 (ite (= (mod j 5) 0) (+ (/ j 5) 1) (+ j 2)))
    )
    (inv j1)
  )
)
