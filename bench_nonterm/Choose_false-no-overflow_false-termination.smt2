(declare-rel inv (Int ))
(declare-var j Int)
(declare-var j1 Int)

(rule (inv 3))

(rule (=> 
    (and 
        (inv j)
        (>= j 3)
        (= j1 (ite (> j 5) (+ j 3) (ite (> j 10) (- j 2) (+ j 1))))
    )
    (inv j1)
  )
)
