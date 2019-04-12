(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes () ((Pair (Pair2 (first list) (second list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun twoThirds (Nat) Nat)
(declare-fun third (Nat) Nat)
(declare-fun take (Nat list) list)
(declare-fun sort2 (Int Int) list)
(declare-fun ordered (list) Bool)
(declare-fun length (list) Nat)
(declare-fun drop (Nat list) list)
(declare-fun splitAt (Nat list) Pair)
(declare-fun append (list list) list)
(declare-fun nstooge2sort2 (list) list)
(declare-fun nstoogesort2 (list) list)
(declare-fun nstooge2sort1 (list) list)
(assert (not (forall ((x list)) (ordered (nstoogesort2 x)))))
(assert
  (forall ((x Nat))
    (= (twoThirds x)
      (ite
        (is-S x)
        (ite
          (is-S (p x))
          (ite (is-S (p (p x))) (S (S (twoThirds (p (p (p x)))))) (S Z))
          (S Z))
        Z))))
(assert
  (forall ((x Nat))
    (= (third x)
      (ite
        (is-S x)
        (ite
          (is-S (p x)) (ite (is-S (p (p x))) (S (third (p (p (p x))))) Z) Z)
        Z))))
(assert
  (forall ((x Nat) (y list))
    (= (take x y)
      (ite
        (is-S x)
        (ite (is-cons y) (cons (head y) (take (p x) (tail y))) nil) nil))))
(assert
  (forall ((x Int) (y Int))
    (= (sort2 x y)
      (ite (<= x y) (cons x (cons y nil)) (cons y (cons x nil))))))
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
  (forall ((x list))
    (= (length x) (ite (is-cons x) (S (length (tail x))) Z))))
(assert
  (forall ((x Nat) (y list))
    (= (drop x y)
      (ite (is-S x) (ite (is-cons y) (drop (p x) (tail y)) nil) y))))
(assert
  (forall ((x Nat) (y list))
    (= (splitAt x y) (Pair2 (take x y) (drop x y)))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(assert
  (forall ((x list))
    (= (nstooge2sort2 x)
      (let ((y (splitAt (twoThirds (length x)) x)))
        (append (nstoogesort2 (first y)) (second y))))))
(assert
  (forall ((x list))
    (= (nstoogesort2 x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (ite
            (is-cons (tail (tail x)))
            (nstooge2sort2
              (nstooge2sort1
                (nstooge2sort2
                  (cons (head x)
                    (cons (head (tail x))
                      (cons (head (tail (tail x))) (tail (tail (tail x)))))))))
            (sort2 (head x) (head (tail x))))
          (cons (head x) nil))
        nil))))
(assert
  (forall ((x list))
    (= (nstooge2sort1 x)
      (let ((y (splitAt (third (length x)) x)))
        (append (first y) (nstoogesort2 (second y)))))))
(check-sat)
