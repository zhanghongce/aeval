(declare-rel inv ( Int Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var k Int)
(declare-var l Int)

(rule (inv i j k l))

; requires --transform 2

(rule (=> 
    (and 
        (inv i j k l)
        (<= i l)
        (<= j k)
        (= i1 j)
        (= j1 (- i 1))
    )
    (inv i1 j1 k l)
  )
)
