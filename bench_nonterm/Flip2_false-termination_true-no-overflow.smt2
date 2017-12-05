(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(rule (inv i j))

(rule (=> 
    (and 
        (inv i j)
        (> i 0)
        (> j 0)
        (= i1 (ite (< i j) j (ite (> i j) i (- i 1))))
        (= j1 (ite (< i j) i (ite (> i j) i j)))
    )
    (inv i1 j1)
  )
)
