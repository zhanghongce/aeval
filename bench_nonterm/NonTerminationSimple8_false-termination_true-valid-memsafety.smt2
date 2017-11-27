(declare-rel inv (Int))
(declare-var j Int)
(declare-var j1 Int)

(declare-rel fail ())

(rule (inv j))

(rule (=> 
    (and 
        (inv j)
        (>= j 0)
        (or
            (= j1 (+ j 1))
            (= j1 (+ j 2))
            (= j1 (+ j 3))
            (= j1 (+ j 4))
            (= j1 -1)
        )
    )
    (inv j1)
  )
)

(rule (=> (and (inv j) (>= j 0)) fail))

(query fail :print-certificate true)
