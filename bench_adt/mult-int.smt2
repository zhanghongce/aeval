;(set-logic ALL)
(declare-fun mult (Int Int) Int)


(assert (forall ((n Int) (m Int)) (= (mult n m) 
	(ite (> m 0) 
		(+ n (mult n (- m 1))) 
		0 ))))



; add is associative lemma
;(assert (forall ((x INT) (y INT) (z INT)) (= (add x (add y z)) (add (add x y) z))))

; add is commutative lemma
;(assert (forall ((x INT) (y INT)) (= (add x y) (add y x))))

;lemma
(assert (forall ((x Int) (y Int)) (= (- (mult x y) y) (mult (- x 1) y))) )
(assert (not (forall ((n Int) (m Int)) (= (mult n m) (mult m n)) )))

(check-sat)


