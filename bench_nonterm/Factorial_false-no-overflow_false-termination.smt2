(declare-rel inv (Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var fac Int)
(declare-var fac1 Int)

(rule (inv 1 j fac))

(rule (=> 
    (and 
        (inv i j fac)
        (not (= fac j))
        (= fac1 (* fac i))
        (= i1 (+ i 1))
    )
    (inv i1 j fac1)
  )
)
