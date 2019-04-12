(declare-sort sk_a 0)
(declare-datatypes ()
  ((list (nil) (cons (head sk_a) (tail list)))))
(declare-fun append (list list) list)
(assert
  (not
    (forall ((xs list) (ys list) (zs list))
      (=> (= (append xs zs) (append ys zs)) (= xs ys)))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(check-sat)
