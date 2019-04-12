(declare-sort fun1 0)
(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-fun lam (Int) fun1)
(declare-fun lam2 (Int) fun1)
(declare-fun apply1 (fun1 Int) Bool)
(declare-fun null (list) Bool)
(declare-fun filter (fun1 list) list)
(declare-fun elem (Int list) Bool)
(declare-fun delete (Int list) list)
(declare-fun isPermutation (list list) Bool)
(declare-fun append (list list) list)
(declare-fun qsort (list) list)
(assert (not (forall ((x list)) (isPermutation (qsort x) x))))
(assert (forall ((x list)) (= (null x) (not (is-cons x)))))
(assert
  (forall ((p fun1) (x list))
    (= (filter p x)
      (ite
        (is-cons x)
        (ite
          (apply1 p (head x)) (cons (head x) (filter p (tail x)))
          (filter p (tail x)))
        nil))))
(assert
  (forall ((x Int) (y list))
    (= (elem x y)
      (ite (is-cons y) (or (= x (head y)) (elem x (tail y))) false))))
(assert
  (forall ((x Int) (y list))
    (= (delete x y)
      (ite
        (is-cons y)
        (ite (= x (head y)) (tail y) (cons (head y) (delete x (tail y))))
        nil))))
(assert
  (forall ((x list) (y list))
    (= (isPermutation x y)
      (ite
        (is-cons x)
        (and (elem (head x) y)
          (isPermutation (tail x) (delete (head x) y)))
        (null y)))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(assert
  (forall ((x list))
    (= (qsort x)
      (ite
        (is-cons x)
        (append
          (append (qsort (filter (lam (head x)) (tail x)))
            (cons (head x) nil))
          (qsort (filter (lam2 (head x)) (tail x))))
        nil))))
(assert (forall ((y Int) (z Int)) (= (apply1 (lam y) z) (<= z y))))
(assert
  (forall ((y Int) (x2 Int)) (= (apply1 (lam2 y) x2) (> x2 y))))
(check-sat)
