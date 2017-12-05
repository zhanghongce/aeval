(declare-rel inv ( Int ))
(declare-var i Int)
(declare-var i1 Int)
(declare-var i2 Int)

(rule (inv i))

(rule (=> 
    (and 
        (inv i)
        (not (= i 0))
        (or
            (and
                (< i 0)
                (= i1 (+ i 2))
                (or (and (< i1 0) (= i2 (- i1)))
                    (and (>= i1 0) (= i2 i1)))
            )

            (and
                (not (< i 0))
                (= i1 (- i 2))
                (= i2 (ite (> i1 0) (- i1) i1))
            )
        )
    )
    (inv i2)
  )
)
