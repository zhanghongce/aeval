(declare-rel inv (Int Int))
(declare-var k Int)
(declare-var k1 Int)
(declare-var i Int)
(declare-var i1 Int)

(rule 
    (=> 
        (= i1 (ite (>= k 0) i -1))
        (inv k i1))
)

(rule (=> (and (inv k i)
        (>= i 0)
        (= k1 k)
    )
    (inv k1 i1 ))
)
