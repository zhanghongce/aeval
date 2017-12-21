(declare-rel inv (Int Int) )
(declare-var x Int)
(declare-var x1 Int)
(declare-var oldx Int)
(declare-var oldx1 Int)

(rule (inv x oldx))
(rule 
    (=>
        (and 
          (inv x oldx )
          (> x 1)
          (<= x (* 2 oldx) )
          (= oldx1 x)
        )
        (inv x1 oldx1 )
    )
)
