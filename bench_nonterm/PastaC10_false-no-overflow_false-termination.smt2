(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var r Int)
(declare-var r1 Int)
(declare-var r2 Int)

(rule (inv i j))

(rule (=> 
    (and 
        (inv i j)
        (>= (- i j) 1)
        (= i1 (- i r))
        (= r2 (+ r1 1))
        (= j1 (+ j r2))
    )
    (inv i1 j1)
  )
)
