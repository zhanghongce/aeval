(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Int) (y Lst)) (= (rev (cons x y)) (append (rev y) (cons x nil)))))

; extra lemmas
(assert (not (forall ((_t_2 Lst) (_t_1 Int) ) (= (rev (append (rev _t_2) (cons _t_1 nil) )) (cons _t_1 _t_2)))))
;(assert (not (forall ((x Lst)) (= (rev (rev x)) x))))
(check-sat)
