(declare-datatypes () ((It (A) (B) (C))))
(declare-datatypes () ((list (nil) (cons (head It) (tail list)))))
(declare-fun eq (It It) Bool)
(declare-fun isPrefix (list list) Bool)
(declare-fun isRelaxedPrefix (list list) Bool)
(declare-fun append (list list) list)
(assert
  (not
    (forall ((xs list) (ys list))
      (isRelaxedPrefix xs (append xs ys)))))
(assert
  (forall ((x It) (y It))
    (= (eq x y)
      (ite (is-C x) (is-C y) (ite (is-B x) (is-B y) (is-A y))))))
(assert
  (forall ((x list) (y list))
    (= (isPrefix x y)
      (ite
        (is-cons x)
        (ite
          (is-cons y)
          (and (eq (head x) (head y)) (isPrefix (tail x) (tail y))) false)
        true))))
(assert
  (forall ((x list) (y list))
    (= (isRelaxedPrefix x y)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (ite
            (is-cons y)
            (ite
              (eq (head x) (head y))
              (isRelaxedPrefix (cons (head (tail x)) (tail (tail x))) (tail y))
              (isPrefix (cons (head (tail x)) (tail (tail x)))
                (cons (head y) (tail y))))
            false)
          true)
        true))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(check-sat)
