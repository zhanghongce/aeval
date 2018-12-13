(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-datatypes () ((Queue (queue (front Lst) (back Lst)))))

(declare-fun len (Lst) Int)
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))
(assert (forall ((x Lst)) (>= (len x) 0)))

(declare-fun qlen (Queue) Int)
(assert (forall ((x Lst) (y Lst)) (= (qlen (queue x y)) (+ (len x) (len y)))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Int) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rev2 (Lst Lst) Lst)
(assert (forall ((a Lst)) (= (rev2 nil a) a)))
(assert (forall ((x Int) (t Lst) (a Lst)) (= (rev2 (cons x t) a) (rev2 t (cons x a)))))

(declare-fun qrev (Lst) Lst)
(assert (forall ((x Lst)) (= (qrev x) (rev2 x nil))))

(declare-fun amortizeQueue (Lst Lst) Queue)
(assert (forall ((x Lst) (y Lst)) (= (amortizeQueue x y)
    (ite (<= (len y) (len x))
    (queue x y)
    (queue (append x (qrev y)) nil)))))

; extra lemmas


(assert (forall ((x Lst)) (= (len (rev2 x nil)) (len x))))



;(assert (forall ((x Lst)) (=> (> (len x) 0) (= (len (rev2 x nil)) (len x)))))

;(forall ((Lst)) ((!((len _lm_v_1)<=0))->((0+(len _lm_v_1))=((len (rev2 _lm_v_1 nil))+0))))

; (len (rev2 (cons _t_1 _t_2) nil))+0)=(0+(len (cons _t_1 _t_2))


(assert (forall ((x Lst) (y Lst)) (= (len (append x y)) (+  (len x)  (len y)))))



; (1+(len (append _t_2 (rev2 _v_1 nil))))+0)=((1+(len _t_2))+(len _v_1)))


(assert (not (forall ((x Lst) (y Lst)) (= (qlen (amortizeQueue x y)) (+ (len x) (len y))))))
(check-sat)

