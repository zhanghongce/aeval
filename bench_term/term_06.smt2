(declare-rel inv (Int ))
(declare-var x Int)
(declare-var x1 Int)

(declare-rel fail ())

(rule (inv 0))

(rule (=> 
    (and 
        (inv x )
        (< x 1000)
        (= x1 (ite (= x 7777) x (+ x 1)))
    )
    (inv x1)
  )
)

(rule (=> (and (inv x) (< x 1000)) fail))

(query fail :print-certificate true)
