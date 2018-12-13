(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rev2 (Lst Lst) Lst)
(assert (forall ((a Lst)) (= (rev2 nil a) a)))
(assert (forall ((x Int) (t Lst) (a Lst)) (= (rev2 (cons x t) a) (rev2 t (cons x a)))))


(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Int) (t Lst)) (= (rev (cons x t)) (append (cons x nil) (rev t)))))

;extra lemmas
;(assert (forall ((x Lst) (a Lst)) (= (rev2 x a) (append (rev2 x nil) a))))

;(assert (forall ((x Lst) (y Lst)) (= (len (append x y)) (+ (len x) (len y)))))


;GOAL

(assert (forall ((x Lst)) (= (rev2 x nil) (rev x))))

(assert (not (forall ((x Lst)) (= (len (rev2 x nil)) (len x)))))

;(assert (not (forall ((x Lst)) (= (len (rev x)) (len x)))))
;(assert (not (forall ((x Lst) (a Lst)) (= (append (rev2 x nil) a) (rev2 x a)))))

(check-sat)


; 1 5 6 7 1 0 8


;
;
;((len (append (rev2 _t_2 nil) (cons _t_1 nil)))=(1+(len _t_2)))
;((len (append (rev2 _t_2 nil) (cons _t_1 nil)))=(len (cons _t_1 _t_2)))
