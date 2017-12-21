(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(rule (inv i j))

(rule (=> 
    (and 
        (inv i j)
        (not (= i 0))
        (not (= j 0))
        (= i1 j)
        (= j1 i)
    )
    (inv i1 j1)
  )
)
