(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))


(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Int) (t Lst)) (= (rev (cons x t)) (append (rev t) (cons x nil)))))

;extra lemmas

;(assert (forall ((x Lst) (y Lst)) (= (len (append x y)) (+ (len x) (len y)))))


;GOAL



(assert (not (forall ((x Lst)) (= (len (rev x)) (len x)))))


(check-sat)


;RUN "--template 2 --candidates 5 --gen-fapp"

