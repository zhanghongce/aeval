(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes () ((Pair (Pair2 (first Bool) (second list)))))
(declare-fun null (list) Bool)
(declare-fun elem (Int list) Bool)
(declare-fun delete (Int list) list)
(declare-fun isPermutation (list list) Bool)
(declare-fun bubble (list) Pair)
(declare-fun bubsort (list) list)
(assert (not (forall ((x list)) (isPermutation (bubsort x) x))))
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
    (= (bubble x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (ite
            (<= (head x) (head (tail x)))
            (let ((y (bubble (cons (head (tail x)) (tail (tail x))))))
              (Pair2 (first y) (cons (head x) (second y))))
            (Pair2 true
              (cons (head (tail x))
                (second (bubble (cons (head x) (tail (tail x))))))))
          (Pair2 false (cons (head x) nil)))
        (Pair2 false nil)))))
(assert
  (forall ((x list))
    (= (bubsort x)
      (let ((y (bubble x))) (ite (first y) (bubsort (second y)) x)))))
(check-sat)
