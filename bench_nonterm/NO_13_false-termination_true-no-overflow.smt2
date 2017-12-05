(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(rule (inv 0 100))

(rule (=> 
    (and 
        (inv i j)
        (< i j)
        (or (and (< 51 j) (= i1 (+ i 1)) (= j1 (- j 1)))
            (and (>= 51 j) (= i1 (- i 1)) (= j1 (+ j 1)))
        )
    )
    (inv i1 j1)
  )
)
