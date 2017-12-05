(declare-rel inv (Int Int ))
(declare-var i Int)
(declare-var i1 Int)
(declare-var up Int)
(declare-var up1 Int)

(rule (inv i 0))

(rule (=> 
    (and 
        (inv i up)
        (> i 0)
        (or
            (and (= i 1) (= up1 1))
            (and (= i 10) (= up1 0))
            (and (not (= i 1)) (not (= i 10)) (= up1 up))
        )
        (or
            (and (= up1 1) (= i1 (+ i 1)))
            (and (not (= up1 1)) (= i1 (- i 1)))
        )
    )
    (inv i1 up1)
  )
)
