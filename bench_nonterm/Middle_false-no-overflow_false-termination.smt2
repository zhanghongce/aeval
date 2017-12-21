(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(rule (inv i j))

(rule (=> 
    (and 
        (inv i j)
        (not (= i j))
        (= i1 (- i 1))
        (= j1 (+ j 1))
    )
    (inv i1 j1)
  )
)
