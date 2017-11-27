(declare-rel inv (Int Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)
(declare-var w Int)
(declare-var w1 Int)

(declare-rel fail ())


(rule (inv x y z w))

(rule (=> 
    (and 
        (inv x y z w)
        (> x 0)
        (> y 0)
        (> z 0)
        (> w 0)
        (or (and (= x1 (- x 1)) (= y1 (+ y 1)) (= z1 (+ z 1)) (= w1 (+ w 1)))
            (and (= x1 (+ x 1)) (= y1 (- y 1)) (= z1 (+ z 1)) (= w1 (+ w 1)))
            (and (= x1 (+ x 1)) (= y1 (+ y 1)) (= z1 (- z 1)) (= w1 (+ w 1)))
            (and (= x1 (+ x 1)) (= y1 (+ y 1)) (= z1 (+ z 1)) (= w1 (- w 1))))
    )
    (inv x1 y1 z1 w1)
  )
)

(rule (=> (and (inv x y z w) (> x 0) (> y 0) (> z 0) (> w 0)) fail))

(query fail :print-certificate true)
