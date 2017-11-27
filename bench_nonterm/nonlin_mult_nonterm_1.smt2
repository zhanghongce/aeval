(declare-rel inv (Int Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)

(declare-rel fail ())

(rule (=> (and (> j d) (> d 1)) (inv j d)))

(rule (=> 
    (and 
        (inv j d)
        (> j 1)
        (= j1 (* j j))
    )
    (inv j1 d)
  )
)

(rule (=> (and (inv j d) (> j 1) ) fail))

(query fail :print-certificate true)
