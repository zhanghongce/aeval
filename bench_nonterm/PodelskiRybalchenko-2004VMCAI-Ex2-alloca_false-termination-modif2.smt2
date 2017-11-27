(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var d Int)
(declare-var d1 Int)

(declare-rel fail ())

(rule (inv x d))

(rule (=> 
    (and 
        (inv x d)
        (or (>= x 0) (< d 0))
        (= x1 (+ (* 2 x) d1))
    )
    (inv x1 d1)
  )
)

(rule (=> (and (inv x d) (or (>= x 0) (< d 0))) fail))

(query fail :print-certificate true)
