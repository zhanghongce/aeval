(declare-sort sk_b 0)
(declare-sort fun1 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk_b) (tail2 list2)))))
(declare-datatypes () ((Pair (Pair2 (first sk_b) (second sk_b)))))
(declare-datatypes ()
  ((list (nil) (cons (head Pair) (tail list)))))
(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-const lam fun1)
(declare-fun apply1 (fun1 Pair) sk_b)
(declare-fun pairs (list2) list)
(declare-fun map2 (fun1 list) list2)
(declare-fun length (list2) Nat)
(declare-fun fst (Pair) sk_b)
(declare-fun evens (list2) list2)
(declare-fun odds (list2) list2)
(declare-fun even (Nat) Bool)
(assert
  (not
    (forall ((xs list2))
      (=> (even (length xs)) (= (map2 lam (pairs xs)) (evens xs))))))
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
  (forall ((f fun1) (x list))
    (= (map2 f x)
      (ite
        (is-cons x) (cons2 (apply1 f (head x)) (map2 f (tail x))) nil2))))
(assert
  (forall ((x list2))
    (= (length x) (ite (is-cons2 x) (S (length (tail2 x))) Z))))
(assert (forall ((x Pair)) (= (fst x) (first x))))
(assert
  (forall ((x list2))
    (= (evens x)
      (ite (is-cons2 x) (cons2 (head2 x) (odds (tail2 x))) nil2))))
(assert
  (forall ((x list2))
    (= (odds x) (ite (is-cons2 x) (evens (tail2 x)) nil2))))
(assert
  (forall ((x Nat))
    (= (even x)
      (ite (is-S x) (ite (is-S (p x)) (even (p (p x))) false) true))))
(assert (forall ((x Pair)) (= (apply1 lam x) (fst x))))
(check-sat)
