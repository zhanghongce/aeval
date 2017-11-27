(declare-rel inv (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)
(declare-rel fail ())

(rule (inv x y ))

; needs two refinements for INIT

(rule (=> 
    (and 
        (inv x y )
        (< x 5)
        (= x1 (- x y))
        (= y1 (+ x y))
    )
    (inv x1 y1 )
  )
)

(rule (=> (and (inv x y ) (< x 5)) fail))

(query fail :print-certificate true)
