(declare-rel inv (Int Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-var z Int)
(declare-var z1 Int)

(rule (inv x y 0))

; requires --transform 3

(rule (=>
  (and
    (inv x y z)
    (> x 0)
    (= x1 (- x y))
    (= y1 (- y z))
    (= z1 (ite (= z 0) 12 (ite (= z 12) -1 0))))
  (inv x1 y1 z1)
  )
)
