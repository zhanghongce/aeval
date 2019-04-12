(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-fun ssort_minimum (Int list) Int)
(declare-fun null (list) Bool)
(declare-fun elem (Int list) Bool)
(declare-fun delete (Int list) list)
(declare-fun isPermutation (list list) Bool)
(declare-fun ssort (list) list)
(assert (not (forall ((x list)) (isPermutation (ssort x) x))))
(assert
  (forall ((x Int) (y list))
    (= (ssort_minimum x y)
      (ite
        (is-cons y)
        (ite
          (<= (head y) x) (ssort_minimum (head y) (tail y))
          (ssort_minimum x (tail y)))
        x))))
(assert (forall ((x list)) (= (null x) (not (is-cons x)))))
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
  (forall ((x list))
    (= (ssort x)
      (ite
        (is-cons x)
        (let ((m (ssort_minimum (head x) (tail x))))
          (cons m (ssort (delete m (cons (head x) (tail x))))))
        nil))))
(check-sat)
