(declare-rel inv (Int Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var flag Int)
(declare-var flag1 Int)
(declare-var range1 Int)
(declare-var range2 Int)

(rule (inv i 1 range1 range2))

(rule (=> 
    (and 
        (inv i flag range1 range2)
        (<= range1 i) (<= i range2)
        (= i1 (ite (and (= flag 1) (< i range2)) (+ i 1)
              (ite (and (= flag -1) (> i range1)) (- i 1) i)))
        (= flag1 (ite (= i range2) -1
                 (ite (= i range1) 1 flag)))
    )
    (inv i1 flag1 range1 range2)
  )
)
