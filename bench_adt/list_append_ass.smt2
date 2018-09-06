(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(assert (not (forall ((x Lst) (y Lst) (z Lst)) (= (append x (append y z)) (append (append x y) z)))))
(check-sat)
