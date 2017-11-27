(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var K Int)
(declare-var N Int)

(declare-rel fail ())

(rule (=> (= N 2) (inv x K N)))

(rule (=> 
    (and 
        (inv x K N)
        (not (= x K))
        (= x1 (ite (> x K) (- x N) (+ x N)))
    )
    (inv x1 K N)
  )
)

(rule (=> (and (inv x K N) (not (= x K))) fail))

(query fail :print-certificate true)
