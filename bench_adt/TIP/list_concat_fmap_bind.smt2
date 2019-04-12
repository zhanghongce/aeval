(declare-sort sk_a 0)
(declare-sort sk_b 0)
(declare-sort fun1 0)
(declare-datatypes ()
  ((list3 (nil2) (cons2 (head2 sk_a) (tail2 list3)))))
(declare-datatypes ()
  ((list2 (nil3) (cons3 (head3 sk_b) (tail3 list2)))))
(declare-datatypes ()
  ((list (nil) (cons (head list2) (tail list)))))
(declare-fun apply1 (fun1 sk_a) list2)
(declare-fun fmap (fun1 list3) list)
(declare-fun append (list2 list2) list2)
(declare-fun bind (list3 fun1) list2)
(declare-fun concat2 (list) list2)
(assert
  (not
    (forall ((f fun1) (xs list3))
      (= (concat2 (fmap f xs)) (bind xs f)))))
(assert
  (forall ((x fun1) (y list3))
    (= (fmap x y)
      (ite
        (is-cons2 y) (cons (apply1 x (head2 y)) (fmap x (tail2 y))) nil))))
(assert
  (forall ((x list2) (y list2))
    (= (append x y)
      (ite (is-cons3 x) (cons3 (head3 x) (append (tail3 x) y)) y))))
(assert
  (forall ((x list3) (y fun1))
    (= (bind x y)
      (ite
        (is-cons2 x) (append (apply1 y (head2 x)) (bind (tail2 x) y))
        nil3))))
(assert
  (forall ((x list))
    (= (concat2 x)
      (ite (is-cons x) (append (head x) (concat2 (tail x))) nil3))))
(check-sat)
