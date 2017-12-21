(declare-rel inv (Int))
(declare-var j Int)
(declare-var j1 Int)

(rule (inv j))

(rule (=> 
    (and 
        (inv j)
        (< j 0)
        (or
            (= j1 (+ j 1))
            (= j1 (- j 1))
        )
    )
    (inv j1)
  )
)
