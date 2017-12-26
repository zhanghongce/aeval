(declare-rel inv (Int Int Int) )
(declare-var x Int)
(declare-var x1 Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var tx Int)
(declare-var tx1 Int)

(rule (inv x z tx))
(rule 
    (=>
        (and 
          (inv x z tx)
          (<= x (+ tx z) )
          (= z1 (- z 1) )
          (= tx1 x)
        )
        (inv x1 z1 tx1)
    )
)
