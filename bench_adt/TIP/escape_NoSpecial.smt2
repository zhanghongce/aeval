(declare-sort fun1 0)
(declare-datatypes () ((Token (A) (B) (C) (D) (ESC) (P) (Q) (R))))
(declare-datatypes ()
  ((list (nil) (cons (head Token) (tail list)))))
(declare-const lam fun1)
(declare-fun apply1 (fun1 Token) Bool)
(declare-fun isSpecial (Token) Bool)
(declare-fun isEsc (Token) Bool)
(declare-fun ok (Token) Bool)
(declare-fun code (Token) Token)
(declare-fun escape (list) list)
(declare-fun all (fun1 list) Bool)
(assert (not (forall ((xs list)) (all lam (escape xs)))))
(assert
  (forall ((x Token))
    (= (isSpecial x)
      (ite
        (is-R x) true
        (ite (is-Q x) true (ite (is-P x) true (is-ESC x)))))))
(assert (forall ((x Token)) (= (isEsc x) (is-ESC x))))
(assert
  (forall ((x Token)) (= (ok x) (or (not (isSpecial x)) (isEsc x)))))
(assert
  (forall ((x Token))
    (= (code x)
      (ite
        (is-R x) C
        (ite (is-Q x) B (ite (is-P x) A (ite (is-ESC x) ESC x)))))))
(assert
  (forall ((x list))
    (= (escape x)
      (ite
        (is-cons x)
        (ite
          (isSpecial (head x))
          (cons ESC (cons (code (head x)) (escape (tail x))))
          (cons (head x) (escape (tail x))))
        nil))))
(assert
  (forall ((x fun1) (y list))
    (= (all x y)
      (ite
        (is-cons y) (and (apply1 x (head y)) (all x (tail y))) true))))
(assert (forall ((x Token)) (= (apply1 lam x) (ok x))))
(check-sat)
