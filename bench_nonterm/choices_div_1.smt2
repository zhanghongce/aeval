(declare-rel inv (Int))
(declare-var j Int)
(declare-var j1 Int)

(rule (=> (>= j 2) (inv j)))

(rule (=> 
    (and 
        (inv j)
        (>= j 0)
        (or
          (= j1 (/ j 2))
          (= j1 (- j 1))
        )
    )
    (inv j1)
  )
)
