(declare-rel inv (Int Int Int))
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var w Int)
(declare-var w1 Int)

(rule (inv y z w))

(rule (=> 
    (and 
        (inv y z w)
        (< (+ (mod y 34) (mod z 34) (mod w 34)) 100)
        (= y1 (+ y 1))
        (= z1 (+ z 2))
        (= w1 (+ w 3))
    )
    (inv y1 z1 w1)
  )
)
