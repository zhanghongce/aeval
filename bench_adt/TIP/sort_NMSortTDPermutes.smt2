(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun take (Nat list) list)
(declare-fun null (list) Bool)
(declare-fun lmerge (list list) list)
(declare-fun length (list) Nat)
(declare-fun half (Nat) Nat)
(declare-fun elem (Int list) Bool)
(declare-fun drop (Nat list) list)
(declare-fun nmsorttd (list) list)
(declare-fun delete (Int list) list)
(declare-fun isPermutation (list list) Bool)
(assert (not (forall ((x list)) (isPermutation (nmsorttd x) x))))
(assert
  (forall ((x Nat) (y list))
    (= (take x y)
      (ite
        (is-S x)
        (ite (is-cons y) (cons (head y) (take (p x) (tail y))) nil) nil))))
(assert (forall ((x list)) (= (null x) (not (is-cons x)))))
(assert
  (forall ((x list) (y list))
    (= (lmerge x y)
      (ite
        (is-cons x)
        (ite
          (is-cons y)
          (ite
            (<= (head x) (head y))
            (cons (head x) (lmerge (tail x) (cons (head y) (tail y))))
            (cons (head y) (lmerge (cons (head x) (tail x)) (tail y))))
          (cons (head x) (tail x)))
        y))))
(assert
  (forall ((x list))
    (= (length x) (ite (is-cons x) (S (length (tail x))) Z))))
(assert
  (forall ((x Nat))
    (= (half x)
      (ite (is-S x) (ite (is-S (p x)) (S (half (p (p x)))) Z) Z))))
(assert
  (forall ((x Int) (y list))
    (= (elem x y)
      (ite (is-cons y) (or (= x (head y)) (elem x (tail y))) false))))
(assert
  (forall ((x Nat) (y list))
    (= (drop x y)
      (ite (is-S x) (ite (is-cons y) (drop (p x) (tail y)) nil) y))))
(assert
  (forall ((x list))
    (= (nmsorttd x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (let
            ((k (half
                  (length (cons (head x) (cons (head (tail x)) (tail (tail x))))))))
            (lmerge
              (nmsorttd
                (take k (cons (head x) (cons (head (tail x)) (tail (tail x))))))
              (nmsorttd
                (drop k (cons (head x) (cons (head (tail x)) (tail (tail x))))))))
          (cons (head x) nil))
        nil))))
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
