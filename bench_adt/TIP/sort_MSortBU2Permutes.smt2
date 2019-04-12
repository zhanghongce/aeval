(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 Int) (tail2 list2)))))
(declare-datatypes ()
  ((list (nil) (cons (head list2) (tail list)))))
(declare-fun risers (list2) list)
(declare-fun null (list2) Bool)
(declare-fun lmerge (list2 list2) list2)
(declare-fun pairwise (list) list)
(declare-fun mergingbu2 (list) list2)
(declare-fun msortbu2 (list2) list2)
(declare-fun elem (Int list2) Bool)
(declare-fun delete (Int list2) list2)
(declare-fun isPermutation (list2 list2) Bool)
(assert (not (forall ((x list2)) (isPermutation (msortbu2 x) x))))
(assert
  (forall ((x list2))
    (= (risers x)
      (ite
        (is-cons2 x)
        (ite
          (is-cons2 (tail2 x))
          (ite
            (<= (head2 x) (head2 (tail2 x)))
            (let ((y (risers (cons2 (head2 (tail2 x)) (tail2 (tail2 x))))))
              (ite (is-cons y) (cons (cons2 (head2 x) (head y)) (tail y)) nil))
            (cons (cons2 (head2 x) nil2)
              (risers (cons2 (head2 (tail2 x)) (tail2 (tail2 x))))))
          (cons (cons2 (head2 x) nil2) nil))
        nil))))
(assert (forall ((x list2)) (= (null x) (not (is-cons2 x)))))
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
    (= (mergingbu2 x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (mergingbu2
            (pairwise (cons (head x) (cons (head (tail x)) (tail (tail x))))))
          (head x))
        nil2))))
(assert
  (forall ((x list2)) (= (msortbu2 x) (mergingbu2 (risers x)))))
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
(check-sat)
