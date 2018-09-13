(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Int) (y Lst)) (= (rev (cons x y)) (append (rev y) (cons x nil)))))

; extra lemmas
(assert (forall ((x Lst)) (= x (append x nil))))
(assert (forall ((x Lst) (y Lst) (z Lst)) (= (append (append x y) z) (append x (append y z)))))


(assert (not (forall ((x Lst) (y Lst)) (= (rev (append x y)) (append (rev y) (rev x))))))
(check-sat)

; 1,3,3,6,5 OR 1,3,3,4,5,1,0,6,5