(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-fun ssort_minimum (Int list) Int)
(declare-fun ordered (list) Bool)
(declare-fun delete (Int list) list)
(declare-fun ssort (list) list)
(assert (not (forall ((x list)) (ordered (ssort x)))))
(assert
  (forall ((x Int) (y list))
    (= (ssort_minimum x y)
      (ite
        (is-cons y)
        (ite
          (<= (head y) x) (ssort_minimum (head y) (tail y))
          (ssort_minimum x (tail y)))
        x))))
(assert
  (forall ((x list))
    (= (ordered x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (and (<= (head x) (head (tail x)))
            (ordered (cons (head (tail x)) (tail (tail x)))))
          true)
        true))))
(assert
  (forall ((x Int) (y list))
    (= (delete x y)
      (ite
        (is-cons y)
        (ite (= x (head y)) (tail y) (cons (head y) (delete x (tail y))))
        nil))))
(assert
  (forall ((x list))
    (= (ssort x)
      (ite
        (is-cons x)
        (let ((m (ssort_minimum (head x) (tail x))))
          (cons m (ssort (delete m (cons (head x) (tail x))))))
        nil))))
(check-sat)
