(declare-rel inv ( Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var d Int)
(declare-var d0 Int)
(declare-var d1 Int)

(rule (=> (and
        (= d0 1)
        (or (= d1 d0) (= d1 (- d0 1)))
        (or (= d d1) (= d (- d1 1)))) (inv x d)))

(rule (=> 
    (and 
        (inv x d)
        (> x 0)
        (= x1 (- x d))
    )
    (inv x1 d)
  )
)
