(declare-rel inv (Int Int Int Int Int Int ))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var k Int)
(declare-var k1 Int)
(declare-var up Int)
(declare-var up1 Int)
(declare-var left Int)
(declare-var left1 Int)
(declare-var closer Int)
(declare-var closer1 Int)

(rule (inv i j k 0 0 0))

(rule (=> 
    (and 
        (inv i j k up left closer)
        (> i 0)
        (> j 0)
        (> k 0)
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
            (and (= k 1) (= closer1 1))
            (and (= k 10) (= closer1 0))
            (and (not (= k 1)) (not (= k 10)) (= closer1 closer))
        )
        (or
            (and (= up1 1) (= i1 (+ i 1)))
            (and (not (= up1 1)) (= i1 (- i 1)))
        )
        (or
            (and (= left1 1) (= j1 (+ j 1)))
            (and (not (= left1 1)) (= j1 (- j 1)))
        )
        (or
            (and (= closer1 1) (= k1 (+ k 1)))
            (and (not (= closer1 1)) (= k1 (- k 1)))
        )
    )
    (inv i1 i1 k up1 left1 closer1)
  )
)
