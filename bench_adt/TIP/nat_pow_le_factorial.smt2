(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun pow (Nat Nat) Nat)
(declare-fun lt (Nat Nat) Bool)
(declare-fun factorial (Nat) Nat)
(assert
  (not
    (forall ((n Nat))
      (lt (pow (S (S Z)) (S (S (S (S n)))))
        (factorial (S (S (S (S n)))))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat) (y Nat))
    (= (mult x y) (ite (is-S x) (plus y (mult (p x) y)) Z))))
(assert
  (forall ((x Nat) (y Nat))
    (= (pow x y) (ite (is-S y) (mult x (pow x (p y))) (S Z)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (lt x y)
      (ite (is-S x) (ite (is-S y) (lt (p x) (p y)) false) true))))
(assert
  (forall ((x Nat))
    (= (factorial x)
      (ite (is-S x) (mult (S (p x)) (factorial (p x))) (S Z)))))
(check-sat)
