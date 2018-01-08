(declare-rel inv (Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)

(rule (inv 0))

(rule (=> 
    (and 
        (inv x )
        (< x 52352)
        (= x1 (* 37 (mod x2 1415)))
    )
    (inv x1)
  )
)
