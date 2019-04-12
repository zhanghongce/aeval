(declare-sort sk_t 0)
(declare-sort fun1 0)
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 sk_t) (tail2 list2)))))
(declare-datatypes () ((Pair (Pair2 (first sk_t) (second sk_t)))))
(declare-datatypes ()
  ((list (nil) (cons (head Pair) (tail list)))))
(declare-const lam fun1)
(declare-fun apply1 (fun1 Pair) sk_t)
(declare-fun snd (Pair) sk_t)
(declare-fun pairs (list2) list)
(declare-fun map2 (fun1 list) list2)
(declare-fun evens (list2) list2)
(declare-fun odds (list2) list2)
(assert
  (not (forall ((xs list2)) (= (map2 lam (pairs xs)) (odds xs)))))
(assert (forall ((x Pair)) (= (snd x) (second x))))
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
    (= (evens x)
      (ite (is-cons2 x) (cons2 (head2 x) (odds (tail2 x))) nil2))))
(assert
  (forall ((x list2))
    (= (odds x) (ite (is-cons2 x) (evens (tail2 x)) nil2))))
(assert (forall ((x Pair)) (= (apply1 lam x) (snd x))))
(check-sat)
