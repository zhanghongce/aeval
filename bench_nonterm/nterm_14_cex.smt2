(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)
(declare-var d1 Int)

(declare-rel fail ())

(rule (inv j d))

(rule (=> 
    (and 
        (inv j d)
        (> d -4)
        (> j -4)
        (or
            (and (= j1 (- j 1)) (= d1 d))
            (and (= d1 d) (= j1 j)))
    )
    (inv j1 d1)
  )
)

(rule (=> (and (inv j d)
  (> d -4)
  (> j -4)
) fail))

(query fail :print-certificate true)
