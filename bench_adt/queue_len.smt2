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


(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Int) (y Lst)) (= (rev (cons x y)) (append (rev y) (cons x nil)))))

(declare-fun amortizeQueue (Lst Lst) Queue)
(assert (forall ((x Lst) (y Lst)) (= (amortizeQueue x y)
    (ite (<= (len y) (len x))
    (queue x y)
    (queue (append x (rev y)) nil)))))

; extra lemmas
;(assert (forall ((x Lst)) (= (len (rev x)) (len x))))
;(assert (forall ((x Lst) (y Lst)) (= (len (append x y)) (+  (len x)  (len y)))))


(assert (not (forall ((x Lst) (y Lst)) (= (qlen (amortizeQueue x y)) (+ (len x) (len y))))))
(check-sat)

;RUN "--template 2 --gen-fapp"