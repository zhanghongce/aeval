(declare-rel inv (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var range Int)
(declare-var range1 Int)

(rule (inv i 20))

(rule (=> 
    (and 
        (inv i range)
        (<= 0 i)
        (<= i range)
        (= i1 (ite (not (and (= 0 i) (= i range))) (ite (= i range) 0 (+ i 1)) i))
        (= range1 (ite (not (and (= 0 i) (= i range))) (ite (= i range) (- range 1) range) range))
    )
    (inv i1 range1)
  )
)
