(declare-rel inv (Int))
(declare-var a Int)
(declare-var a1 Int)

; requires --transform 3

(rule (inv a))

(rule (=> 
    (and 
        (inv a)
        (> a 1)
        (= a1 (ite (= (mod a 3) 0) (div a 3) (+ a 2)))
    )
    (inv a1)
  )
)
