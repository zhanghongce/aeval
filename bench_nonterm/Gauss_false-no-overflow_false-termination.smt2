(declare-rel inv (Int Int ))
(declare-var n Int)
(declare-var n1 Int)
(declare-var sum Int)
(declare-var sum1 Int)

(rule (inv n 0))

(rule (=> 
    (and 
        (inv n sum)
        (not (= n 0))
        (= sum1 (+ sum n))
        (= n1 (- n 1))
    )
    (inv n1 sum1)
  )
)
