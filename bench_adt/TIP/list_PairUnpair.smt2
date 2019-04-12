(declare-sort sk_t 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk_t) (tail2 list2)))))
(declare-datatypes () ((Pair (Pair2 (first sk_t) (second sk_t)))))
(declare-datatypes ()
  ((list (nil) (cons (head Pair) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-fun unpair (list) list2)
(declare-fun pairs (list2) list)
(declare-fun length (list2) Nat)
(declare-fun even (Nat) Bool)
(assert
  (not
    (forall ((xs list2))
      (=> (even (length xs)) (= (unpair (pairs xs)) xs)))))
(assert
  (forall ((x list))
    (= (unpair x)
      (ite
        (is-cons x)
        (cons2 (first (head x))
          (cons2 (second (head x)) (unpair (tail x))))
        nil2))))
(assert
  (forall ((x list2))
    (= (pairs x)
      (ite
        (is-cons2 x)
        (ite
          (is-cons2 (tail2 x))
          (cons (Pair2 (head2 x) (head2 (tail2 x)))
            (pairs (tail2 (tail2 x))))
          nil)
        nil))))
(assert
  (forall ((x list2))
    (= (length x) (ite (is-cons2 x) (S (length (tail2 x))) Z))))
(assert
  (forall ((x Nat))
    (= (even x)
      (ite (is-S x) (ite (is-S (p x)) (even (p (p x))) false) true))))
(check-sat)
