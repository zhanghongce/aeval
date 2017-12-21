(declare-rel inv (Int ))
(declare-var j Int)
(declare-var j1 Int)

(rule (inv j ))

(rule (=> 
    (and 
        (inv j)
        (> (* j j) 9)
        (= j1 (ite (< j 0) (- j 1) (+ j 1)))
    )
    (inv j1)
  )
)
