(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-fun ordered (list) Bool)
(declare-fun insert2 (Int list) list)
(declare-fun isort (list) list)
(assert (not (forall ((x list)) (ordered (isort x)))))
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
(check-sat)
