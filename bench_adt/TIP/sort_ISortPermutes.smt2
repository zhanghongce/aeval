(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-fun null (list) Bool)
(declare-fun insert2 (Int list) list)
(declare-fun isort (list) list)
(declare-fun elem (Int list) Bool)
(declare-fun delete (Int list) list)
(declare-fun isPermutation (list list) Bool)
(assert (not (forall ((x list)) (isPermutation (isort x) x))))
(assert (forall ((x list)) (= (null x) (not (is-cons x)))))
(assert
  (forall ((x Int) (y list))
    (= (insert2 x y)
      (ite
        (is-cons y)
        (ite
          (<= x (head y)) (cons x (cons (head y) (tail y)))
          (cons (head y) (insert2 x (tail y))))
        (cons x nil)))))
(assert
  (forall ((x list))
    (= (isort x)
      (ite (is-cons x) (insert2 (head x) (isort (tail x))) nil))))
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
(check-sat)
