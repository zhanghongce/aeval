(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes ()
  ((Tree (Node (Node_0 Tree) (Node_1 Nat) (Node_2 Tree)) (Nil))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-fun null (list) Bool)
(declare-fun le (Nat Nat) Bool)
(declare-fun flatten (Tree list) list)
(declare-fun equal (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(declare-fun delete (Nat list) list)
(declare-fun isPermutation (list list) Bool)
(declare-fun add (Nat Tree) Tree)
(declare-fun toTree (list) Tree)
(declare-fun tsort (list) list)
(assert (not (forall ((x list)) (isPermutation (tsort x) x))))
(assert (forall ((x list)) (= (null x) (not (is-cons x)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (le x y)
      (ite (is-S x) (ite (is-S y) (le (p x) (p y)) false) true))))
(assert
  (forall ((x Tree) (y list))
    (= (flatten x y)
      (ite
        (is-Nil x) y
        (flatten (Node_0 x) (cons (Node_1 x) (flatten (Node_2 x) y)))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (equal x y)
      (ite
        (is-S x) (ite (is-S y) (equal (p x) (p y)) false)
        (not (is-S y))))))
(assert
  (forall ((x Nat) (y list))
    (= (elem x y)
      (ite
        (is-cons y) (or (equal x (head y)) (elem x (tail y))) false))))
(assert
  (forall ((x Nat) (y list))
    (= (delete x y)
      (ite
        (is-cons y)
        (ite
          (equal x (head y)) (tail y) (cons (head y) (delete x (tail y))))
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
  (forall ((x Nat) (y Tree))
    (= (add x y)
      (ite
        (is-Nil y) (Node Nil x Nil)
        (ite
          (le x (Node_1 y)) (Node (add x (Node_0 y)) (Node_1 y) (Node_2 y))
          (Node (Node_0 y) (Node_1 y) (add x (Node_2 y))))))))
(assert
  (forall ((x list))
    (= (toTree x)
      (ite (is-cons x) (add (head x) (toTree (tail x))) Nil))))
(assert (forall ((x list)) (= (tsort x) (flatten (toTree x) nil))))
(check-sat)
