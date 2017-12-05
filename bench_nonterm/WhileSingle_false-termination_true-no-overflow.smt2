(declare-rel inv (Int))
(declare-var j Int)
(declare-var j1 Int)

(rule (inv j))

(rule (=> 
    (and 
        (inv j)
        (< j 10)
        (= j1 (ite (not (= j 3)) (+ j 1) j))
    )
    (inv j1)
  )
)
