(declare-rel inv (Int Int) )
(declare-var a Int)
(declare-var a1 Int)
(declare-var b Int)
(declare-var b1 Int)

(rule (inv a b))
(rule 
    (=>
        (and 
            (inv a b )
            (>= a 7)
            (= a1 b)
            (= b1 (+ a 1))
        )
        (inv a1 b1 )
    )
)
