(declare-sort fun1 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 Int) (tail2 list2)))))
(declare-datatypes ()
  ((list (nil) (cons (head list2) (tail list)))))
(declare-const lam fun1)
(declare-fun apply1 (fun1 Int) list2)
(declare-fun null (list2) Bool)
(declare-fun map2 (fun1 list2) list)
(declare-fun lmerge (list2 list2) list2)
(declare-fun pairwise (list) list)
(declare-fun mergingbu (list) list2)
(declare-fun msortbu (list2) list2)
(declare-fun elem (Int list2) Bool)
(declare-fun delete (Int list2) list2)
(declare-fun isPermutation (list2 list2) Bool)
(assert (not (forall ((x list2)) (isPermutation (msortbu x) x))))
(assert (forall ((x list2)) (= (null x) (not (is-cons2 x)))))
(assert
  (forall ((f fun1) (x list2))
    (= (map2 f x)
      (ite
        (is-cons2 x) (cons (apply1 f (head2 x)) (map2 f (tail2 x))) nil))))
(assert
  (forall ((x list2) (y list2))
    (= (lmerge x y)
      (ite
        (is-cons2 x)
        (ite
          (is-cons2 y)
          (ite
            (<= (head2 x) (head2 y))
            (cons2 (head2 x) (lmerge (tail2 x) (cons2 (head2 y) (tail2 y))))
            (cons2 (head2 y) (lmerge (cons2 (head2 x) (tail2 x)) (tail2 y))))
          (cons2 (head2 x) (tail2 x)))
        y))))
(assert
  (forall ((x list))
    (= (pairwise x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (cons (lmerge (head x) (head (tail x))) (pairwise (tail (tail x))))
          (cons (head x) nil))
        nil))))
(assert
  (forall ((x list))
    (= (mergingbu x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (mergingbu
            (pairwise (cons (head x) (cons (head (tail x)) (tail (tail x))))))
          (head x))
        nil2))))
(assert
  (forall ((x list2)) (= (msortbu x) (mergingbu (map2 lam x)))))
(assert
  (forall ((x Int) (y list2))
    (= (elem x y)
      (ite (is-cons2 y) (or (= x (head2 y)) (elem x (tail2 y))) false))))
(assert
  (forall ((x Int) (y list2))
    (= (delete x y)
      (ite
        (is-cons2 y)
        (ite
          (= x (head2 y)) (tail2 y) (cons2 (head2 y) (delete x (tail2 y))))
        nil2))))
(assert
  (forall ((x list2) (y list2))
    (= (isPermutation x y)
      (ite
        (is-cons2 x)
        (and (elem (head2 x) y)
          (isPermutation (tail2 x) (delete (head2 x) y)))
        (null y)))))
(assert (forall ((y Int)) (= (apply1 lam y) (cons2 y nil2))))
(check-sat)
