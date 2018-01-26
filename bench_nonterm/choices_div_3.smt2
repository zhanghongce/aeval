(declare-rel inv (Int))
(declare-var j Int)
(declare-var j1 Int)

(rule (=> (>= j 10) (inv j)))

(rule (=> 
    (and 
        (inv j)
        (>= j 0)
        (or
          (= j1 (/ j 2))
          (= j1 (+ (/ j 3) 1))
          (= j1 -90)
        )
    )
    (inv j1)
  )
)
