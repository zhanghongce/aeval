(declare-rel inv (Int Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var flag Int)
(declare-var flag1 Int)
(declare-var range1 Int)
(declare-var range2 Int)
(declare-var range3 Int)
(declare-var range4 Int)

(rule (=> (and (< range1 0) (> range2 0)) (inv i 1 range1 range2)))

(rule (=> 
    (and 
        (inv i flag range1 range2)
        (<= range1 i) (<= i range2)
        (= i1 (ite (and (= flag 1) (< i range2)) (+ i 1)
              (ite (and (= flag -1) (> i range1)) (- i 1) i)))
        (= flag1 (ite (= i range2) -1
                 (ite (= i range1) 1 flag)))
        (= range3 (ite (= i range2) (* 2 range1) range1))
        (= range4 (ite (= i range1) (* 2 range2) range2))
    )
    (inv i1 flag1 range3 range4)
  )
)
