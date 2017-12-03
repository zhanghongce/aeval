(declare-rel inv (Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var k Int)
(declare-var k1 Int)

; requires --transform 2

(rule (inv i j k))

(rule (=> 
    (and 
        (inv i j k)
        (<= i 100)
        (<= j k)
        (> k -1073741824)
        (= i1 j)
        (= j1 i)
        (= k1 (+ i1 j1))
    )
    (inv i1 j1 k1)
  )
)
