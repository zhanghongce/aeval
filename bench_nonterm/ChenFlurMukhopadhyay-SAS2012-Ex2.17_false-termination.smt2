(declare-rel inv (Int Int))

(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)
(declare-var d1 Int)

(declare-rel fail ())

(rule (inv j d))

(rule (=> 
    (and 
        (inv j d)
        (< j 10)
        (= j1 (- d))
        (= d1 (+ d 1))
    )
    (inv j1 d1)
  )
)

(rule (=> (and (inv j d)
    (< j 10)
) fail))

(query fail :print-certificate true)
