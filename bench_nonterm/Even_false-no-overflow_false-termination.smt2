(declare-rel inv (Int ))
(declare-var j Int)
(declare-var j1 Int)

(rule (inv j ))

(rule (=> 
    (and 
        (inv j)
        (not (= j 0))
        (not (= j 1))
        (= j1 (- j 2))
    )
    (inv j1)
  )
)
