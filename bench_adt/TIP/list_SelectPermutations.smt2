(declare-sort fun1 0)
(declare-datatypes ()
  ((list2 (nil3) (cons3 (head3 Int) (tail3 list2)))))
(declare-datatypes ()
  ((list (nil) (cons (head list2) (tail list)))))
(declare-datatypes () ((Pair (Pair2 (first Int) (second list2)))))
(declare-datatypes ()
  ((list3 (nil2) (cons2 (head2 Pair) (tail2 list3)))))
(declare-fun lam (list2) fun1)
(declare-fun apply1 (fun1 list2) Bool)
(declare-fun select3 (Int list3) list3)
(declare-fun select2 (list2) list3)
(declare-fun prop_SelectPermutations (list3) list)
(declare-fun null (list2) Bool)
(declare-fun elem (Int list2) Bool)
(declare-fun delete (Int list2) list2)
(declare-fun isPermutation (list2 list2) Bool)
(declare-fun all (fun1 list) Bool)
(assert
  (not
    (forall ((xs list2))
      (all (lam xs) (prop_SelectPermutations (select2 xs))))))
(assert
  (forall ((x Int) (y list3))
    (= (select3 x y)
      (ite
        (is-cons2 y)
        (cons2 (Pair2 (first (head2 y)) (cons3 x (second (head2 y))))
          (select3 x (tail2 y)))
        nil2))))
(assert
  (forall ((x list2))
    (= (select2 x)
      (ite
        (is-cons3 x)
        (cons2 (Pair2 (head3 x) (tail3 x))
          (select3 (head3 x) (select2 (tail3 x))))
        nil2))))
(assert
  (forall ((x list3))
    (= (prop_SelectPermutations x)
      (ite
        (is-cons2 x)
        (cons (cons3 (first (head2 x)) (second (head2 x)))
          (prop_SelectPermutations (tail2 x)))
        nil))))
(assert (forall ((x list2)) (= (null x) (not (is-cons3 x)))))
(assert
  (forall ((x Int) (y list2))
    (= (elem x y)
      (ite (is-cons3 y) (or (= x (head3 y)) (elem x (tail3 y))) false))))
(assert
  (forall ((x Int) (y list2))
    (= (delete x y)
      (ite
        (is-cons3 y)
        (ite
          (= x (head3 y)) (tail3 y) (cons3 (head3 y) (delete x (tail3 y))))
        nil3))))
(assert
  (forall ((x list2) (y list2))
    (= (isPermutation x y)
      (ite
        (is-cons3 x)
        (and (elem (head3 x) y)
          (isPermutation (tail3 x) (delete (head3 x) y)))
        (null y)))))
(assert
  (forall ((x fun1) (y list))
    (= (all x y)
      (ite
        (is-cons y) (and (apply1 x (head y)) (all x (tail y))) true))))
(assert
  (forall ((xs list2) (x list2))
    (= (apply1 (lam xs) x) (isPermutation x xs))))
(check-sat)
