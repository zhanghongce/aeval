(declare-rel inv (Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)

(declare-rel fail ())

(rule (inv j))

(rule (=> 
    (and 
        (inv j)
        (< j 10)
        (= j1 (+ j d))
    )
    (inv j1)
  )
)

(rule (=> (and (inv j)
    (< j 10)
) fail))

(query fail :print-certificate true)
