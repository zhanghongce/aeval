(declare-rel inv (Int Int Int Int ))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var up Int)
(declare-var up1 Int)
(declare-var left Int)
(declare-var left1 Int)

(rule (inv i j 0 0))

(rule (=> 
    (and 
        (inv i j up left)
        (> i 0)
        (> j 0)
        (or
            (and (= i 1) (= up1 1))
            (and (= i 10) (= up1 0))
            (and (not (= i 1)) (not (= i 10)) (= up1 up))
        )
        (or
            (and (= j 1) (= left1 1))
            (and (= j 10) (= left1 0))
            (and (not (= j 1)) (not (= j 10)) (= left1 left))
        )
        (or
            (and (= up1 1) (= i1 (+ i 1)))
            (and (not (= up1 1)) (= i1 (- i 1)))
        )
        (or
            (and (= left1 1) (= j1 (+ j 1)))
            (and (not (= left1 1)) (= j1 (- j 1)))
        )
    )
    (inv i1 i1 up1 left1)
  )
)
