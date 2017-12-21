(declare-rel inv (Int Int))
(declare-var a Int)
(declare-var a1 Int)
(declare-var b Int)
(declare-var b1 Int)
(declare-var r Int)

(rule (inv a b))

(rule (=> 
    (and 
        (inv a b)
        (> b 0)
        (= b1 (- (- a 1) r))
        (= a1 (- (- a 1) r))
    )
    (inv a1 b1)
  )
)
