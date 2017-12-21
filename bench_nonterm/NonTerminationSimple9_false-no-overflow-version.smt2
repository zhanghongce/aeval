(declare-rel inv (Int) )
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)

(rule (inv x))
(rule 
    (=>
        (and 
          (inv x)
          (>= 0 x)
          (= x1 (- x x2))
        )
        (inv x1 )
    )
)
