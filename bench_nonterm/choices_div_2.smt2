(declare-rel inv (Int Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)

(rule (=> (and (> j d) (> d 1)) (inv j d)))

(rule (=> 
    (and 
        (inv j d)
        (>= j 0)
        (or
          (= j1 (/ j 2))
          (= j1 (- j d))
        )
    )
    (inv j1 d)
  )
)
