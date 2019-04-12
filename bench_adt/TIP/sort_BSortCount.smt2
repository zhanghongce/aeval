(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun sort2 (Int Int) list)
(declare-fun evens (list) list)
(declare-fun odds (list) list)
(declare-fun count (Int list) Nat)
(declare-fun append (list list) list)
(declare-fun pairs (list list) list)
(declare-fun stitch (list list) list)
(declare-fun bmerge (list list) list)
(declare-fun bsort (list) list)
(assert
  (not
    (forall ((x Int) (y list)) (= (count x (bsort y)) (count x y)))))
(assert
  (forall ((x Int) (y Int))
    (= (sort2 x y)
      (ite (<= x y) (cons x (cons y nil)) (cons y (cons x nil))))))
(assert
  (forall ((x list))
    (= (evens x)
      (ite (is-cons x) (cons (head x) (odds (tail x))) nil))))
(assert
  (forall ((x list))
    (= (odds x) (ite (is-cons x) (evens (tail x)) nil))))
(assert
  (forall ((x Int) (y list))
    (= (count x y)
      (ite
        (is-cons y)
        (ite (= x (head y)) (S (count x (tail y))) (count x (tail y)))
        Z))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(assert
  (forall ((x list) (y list))
    (= (pairs x y)
      (ite
        (is-cons x)
        (ite
          (is-cons y)
          (append (sort2 (head x) (head y)) (pairs (tail x) (tail y)))
          (cons (head x) (tail x)))
        y))))
(assert
  (forall ((x list) (y list))
    (= (stitch x y)
      (ite (is-cons x) (cons (head x) (pairs (tail x) y)) y))))
(assert
  (forall ((x list) (y list))
    (= (bmerge x y)
      (ite
        (is-cons x)
        (ite
          (is-cons y)
          (ite
            (is-cons (tail x))
            (stitch
              (bmerge
                (evens (cons (head x) (cons (head (tail x)) (tail (tail x)))))
                (evens (cons (head y) (tail y))))
              (bmerge
                (odds (cons (head x) (cons (head (tail x)) (tail (tail x)))))
                (odds (cons (head y) (tail y)))))
            (ite
              (is-cons (tail y))
              (stitch
                (bmerge (evens (cons (head x) nil))
                  (evens (cons (head y) (cons (head (tail y)) (tail (tail y))))))
                (bmerge (odds (cons (head x) nil))
                  (odds (cons (head y) (cons (head (tail y)) (tail (tail y)))))))
              (sort2 (head x) (head y))))
          (cons (head x) (tail x)))
        nil))))
(assert
  (forall ((x list))
    (= (bsort x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (bmerge
            (bsort
              (evens (cons (head x) (cons (head (tail x)) (tail (tail x))))))
            (bsort
              (odds (cons (head x) (cons (head (tail x)) (tail (tail x)))))))
          (cons (head x) nil))
        nil))))
(check-sat)
