(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes () ((Pair (Pair2 (first list) (second list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun third (Nat) Nat)
(declare-fun take (Nat list) list)
(declare-fun sort2 (Int Int) list)
(declare-fun ordered (list) Bool)
(declare-fun length (list) Nat)
(declare-fun drop (Nat list) list)
(declare-fun splitAt (Nat list) Pair)
(declare-fun append (list list) list)
(declare-fun reverse (list) list)
(declare-fun nstooge1sort2 (list) list)
(declare-fun nstoogesort (list) list)
(declare-fun nstooge1sort1 (list) list)
(assert (not (forall ((x list)) (ordered (nstoogesort x)))))
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
    (= (reverse x)
      (ite
        (is-cons x) (append (reverse (tail x)) (cons (head x) nil)) nil))))
(assert
  (forall ((x list))
    (= (nstooge1sort2 x)
      (let ((y (splitAt (third (length x)) (reverse x))))
        (append (nstoogesort (second y)) (reverse (first y)))))))
(assert
  (forall ((x list))
    (= (nstoogesort x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (ite
            (is-cons (tail (tail x)))
            (nstooge1sort2
              (nstooge1sort1
                (nstooge1sort2
                  (cons (head x)
                    (cons (head (tail x))
                      (cons (head (tail (tail x))) (tail (tail (tail x)))))))))
            (sort2 (head x) (head (tail x))))
          (cons (head x) nil))
        nil))))
(assert
  (forall ((x list))
    (= (nstooge1sort1 x)
      (let ((y (splitAt (third (length x)) x)))
        (append (first y) (nstoogesort (second y)))))))
(check-sat)
