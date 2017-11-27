(declare-rel inv ( Int Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var k Int)
(declare-var k1 Int)

(declare-rel fail ())

; i = -1, j = 1, k = -1

(rule (inv i j k))

(rule (=> 
    (and 
        (inv i j k)
        (< i 0)
        (= i1 (+ i k))
        (= k1 (* -2 j))
        (= j1 (+ j 1))
    )
    (inv i1 j1 k1)
  )
)

(rule (=> (and (inv i j k) (< i 0)) fail))

(query fail :print-certificate true)
