(declare-rel inv (Int))
(declare-var x Int)
(declare-var x1 Int)

(declare-rel fail ())

(rule (inv x))

(rule (=> 
    (and 
        (inv x)
        (not (= x 10))
        (= x1 (ite (= (mod x 5) 1) (- x 2) (- x 1)))
    )
    (inv x1)
  )
)

(rule (=> (and (inv x) (not (= x 10))) fail))

(query fail :print-certificate true)
