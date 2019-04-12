(declare-datatypes () ((Token (A) (B) (C) (D) (ESC) (P) (Q) (R))))
(declare-datatypes ()
  ((list (nil) (cons (head Token) (tail list)))))
(declare-fun isSpecial (Token) Bool)
(declare-fun code (Token) Token)
(declare-fun escape (list) list)
(assert
  (not
    (forall ((xs list) (ys list))
      (=> (= (escape xs) (escape ys)) (= xs ys)))))
(assert
  (forall ((x Token))
    (= (isSpecial x)
      (ite
        (is-R x) true
        (ite (is-Q x) true (ite (is-P x) true (is-ESC x)))))))
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
(check-sat)
