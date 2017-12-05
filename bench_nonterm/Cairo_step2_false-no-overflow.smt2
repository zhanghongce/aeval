(declare-rel inv (Int))
(declare-var j Int)
(declare-var j1 Int)

(rule (=> (> j 0) (inv j)))

(rule (=> 
    (and 
        (inv j)
        (not (= j 0))
        (= j1 (- j 2))
    )
    (inv j1)
  )
)
