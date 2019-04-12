(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun mult (Nat Nat) Nat)
(declare-fun pow (Nat Nat) Nat)
(assert
  (not
    (forall ((n Nat) (x Nat) (y Nat) (z Nat))
      (distinct
        (plus (pow (S x) (S (S (S n)))) (pow (S y) (S (S (S n)))))
        (pow (S z) (S (S (S n))))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Nat) (y Nat))
    (= (mult x y) (ite (is-S x) (plus y (mult (p x) y)) Z))))
(assert
  (forall ((x Nat) (y Nat))
    (= (pow x y) (ite (is-S y) (mult x (pow x (p y))) (S Z)))))
(check-sat)
