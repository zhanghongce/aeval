(declare-sort fun1 0)
(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-fun lam (Int) fun1)
(declare-fun lam2 (Int) fun1)
(declare-fun apply1 (fun1 Int) Bool)
(declare-fun ordered (list) Bool)
(declare-fun filter (fun1 list) list)
(declare-fun append (list list) list)
(declare-fun qsort (list) list)
(assert (not (forall ((x list)) (ordered (qsort x)))))
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
  (forall ((p fun1) (x list))
    (= (filter p x)
      (ite
        (is-cons x)
        (ite
          (apply1 p (head x)) (cons (head x) (filter p (tail x)))
          (filter p (tail x)))
        nil))))
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
