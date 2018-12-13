(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Int) (y Lst)) (= (rev (cons x y)) (append (rev y) (cons x nil)))))

(assert (forall ((x Lst) (y Lst) (z Lst)) (= (append (append x y) z) (append x (append y z)))))

; extra lemmas
;(assert (forall ((x Lst) (y Lst)) (= (rev (append x y)) (append (rev y) (rev x)))))


;(assert (forall ((x Lst) (y Lst)) (= (rev (append (rev x) y)) (append (rev y) x))))

;(assert (forall ((x Lst) (y Lst)) (= (rev (append x y)) (append (rev y) (rev x)))))

;((rev (append (rev _t_2) (cons _t_1 nil)))=(cons _t_1 _t_2))
;(append (cons _t_1 nil) _t_2)


;((rev (append (rev _t_2) (cons _t_1 nil)))=(cons _t_1 _t_2))

;(assert (not (forall ((x Lst) (n Int))  (= (rev (append (rev x) (cons n nil)))(cons n x)))))

(assert (not (forall ((x Lst)) (= (rev (rev x)) x))))



; 3,4,3,2,0,1,0,5
