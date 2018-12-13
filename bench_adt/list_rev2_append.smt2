(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

;(assert (forall ((n Int) (x Lst)) (= (cons n x) (append (cons n nil) x))))

(declare-fun rev2 (Lst Lst) Lst)
(assert (forall ((a Lst)) (= (rev2 nil a) a)))
(assert (forall ((x Int) (t Lst) (a Lst)) (= (rev2 (cons x t) a) (rev2 t (cons x a)))))

; extra lemma
(assert (forall ((x Lst) (y Lst) (z Lst)) (= (append (append x y) z) (append x (append y z)))))

(assert (not (forall ((x Lst) (a Lst)) (= (rev2 x a) (append (rev2 x nil) a)))))
(check-sat)









;Assumptions [4]: (forall ((Lst)) ((rev2 _t_2 a)=(append (rev2 _t_2 nil) a)))
;current goal: ((append (rev2 _t_2 nil) (cons _t_1 _v_1))=(append (rev2 _t_2 (cons _t_1 nil)) _v_1))
;apply on LHS (unwanted): ((append (append (rev2 _t_2 nil) nil) (cons _t_1 _v_1))= …
;apply on RHS (desired): ((append (rev2 _t_2 nil) (cons _t_1 _v_1))=(append (append ;(rev2 _t_2 nil) (cons _t_1 nil)) _v_1