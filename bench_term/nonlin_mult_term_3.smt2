(declare-rel inv (Int Int Int))
(declare-var j Int)
(declare-var j1 Int)
(declare-var d Int)
(declare-var m Int)
(declare-var m1 Int)

(declare-rel fail ())

(rule (=> (and (> j 0) (> m 0) (> d 1)) (inv j m d)))

(rule (=> 
    (and 
        (inv j m d)
        (< j 100)
        (= j1 (* j d m))
        (= m1 (+ m 1))
    )
    (inv j1 m1 d)
  )
)

(rule (=> (and (inv j m d) (< j 100) ) fail))

(query fail :print-certificate true)
