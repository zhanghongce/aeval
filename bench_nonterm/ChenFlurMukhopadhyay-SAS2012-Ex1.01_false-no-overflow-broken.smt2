(declare-rel inv ( Int Int ))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)

(rule (inv x y))

(rule (=>
  (and
    (inv x y)
    (> (+ x y) 0)
    (= x1 (+ (* -5 x) (* -6 y) 18))
  )
  (inv x1 y)
))

