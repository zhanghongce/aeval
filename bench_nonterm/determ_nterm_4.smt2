(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var x2 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

; requires --solver spacer

(rule (inv 1 2 3))

(rule (=> 
    (and 
        (inv x y z)
        (< (+ x y z) 10)
        (= x1 (- x y))
        (= y1 (+ x1 y))
        (= z1 (+ z x1))
        (= x2 (- y1 x1))
    )
    (inv x2 y1 z1)
  )
)
