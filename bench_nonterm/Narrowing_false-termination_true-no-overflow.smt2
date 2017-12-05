(declare-rel inv (Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var up Int)
(declare-var up1 Int)
(declare-var range Int)
(declare-var range1 Int)

(rule (inv i 20 0))

(rule (=> 
    (and 
        (inv i range up)
        (<= 0 i)
        (<= i range)
        (or
            (and (= i 0) (= up1 1))
            (and (= i range) (= up1 0))
            (and (not (= i 0)) (not (= i range)) (= up1 up))
        )
        (or
            (and (= up1 1) (= i1 (+ i 1)))
            (and (= up1 0) (= i1 (- i 1)))
            (and (not (= up1 0)) (not (= up1 1)) (= i1 i))
        )
        (= range1 (ite (= i1 (- range 2)) (- range 1) range))
    )
    (inv i1 range1 up1)
  )
)
