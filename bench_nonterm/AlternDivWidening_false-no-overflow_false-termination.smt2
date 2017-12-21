(declare-rel inv ( Int Int ))
(declare-var i Int)
(declare-var i1 Int)
(declare-var w Int)
(declare-var w1 Int)

; requires --transform 2

(rule (inv i 5))

(rule (=>
    (and
      (inv i w)
      (not (= i 0))
      (= w1 (+ w 1))
      (= i1 (ite (< i (- w)) (+ 1 (- i)) (ite (> i w) (+ (- i) -1) 0)))
    )
    (inv i1 w1)
))
