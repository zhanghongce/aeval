(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-datatypes ()
  ((list4 (nil4) (cons4 (head4 Bool) (tail4 list4)))))
(declare-datatypes ()
  ((list3 (nil3) (cons3 (head3 Int) (tail3 list3)))))
(declare-datatypes () ((Pair (Pair2 (first Int) (second Bool)))))
(declare-datatypes ()
  ((list2 (nil2) (cons2 (head2 Pair) (tail2 list2)))))
(declare-datatypes ()
  ((list (nil) (cons (head list2) (tail list)))))
(declare-datatypes ()
  ((Form (& (&_0 Form) (&_1 Form))
     (Not (Not_0 Form)) (Var (Var_0 Int)))))
(declare-const lam fun12)
(declare-fun lam2 (Int) fun13)
(declare-fun lam3 (Int) fun13)
(declare-const lam4 fun1)
(declare-fun apply1 (fun1 list2) Bool)
(declare-fun apply12 (fun12 Pair) Int)
(declare-fun apply13 (fun13 Pair) Bool)
(declare-fun or2 (list4) Bool)
(declare-fun models4 (Int list2) list4)
(declare-fun models3 (Int list2) list4)
(declare-fun map2 (fun12 list2) list3)
(declare-fun fst (Pair) Int)
(declare-fun filter (fun13 list2) list2)
(declare-fun elem (Int list3) Bool)
(declare-fun okay (list2) Bool)
(declare-fun append (list list) list)
(declare-fun models (Form list2) list)
(declare-fun models2 (Form list) list)
(declare-fun models5 (Form list list) list)
(declare-fun all (fun1 list) Bool)
(assert (not (forall ((p Form)) (all lam4 (models p nil2)))))
(assert
  (forall ((x list4))
    (= (or2 x)
      (ite (is-cons4 x) (or (head4 x) (or2 (tail4 x))) false))))
(assert
  (forall ((x Int) (y list2))
    (= (models4 x y)
      (ite
        (is-cons2 y)
        (ite
          (second (head2 y)) (models4 x (tail2 y))
          (cons4 (= x (first (head2 y))) (models4 x (tail2 y))))
        nil4))))
(assert
  (forall ((x Int) (y list2))
    (= (models3 x y)
      (ite
        (is-cons2 y)
        (ite
          (second (head2 y))
          (cons4 (= x (first (head2 y))) (models3 x (tail2 y)))
          (models3 x (tail2 y)))
        nil4))))
(assert
  (forall ((f fun12) (x list2))
    (= (map2 f x)
      (ite
        (is-cons2 x) (cons3 (apply12 f (head2 x)) (map2 f (tail2 x)))
        nil3))))
(assert (forall ((x Pair)) (= (fst x) (first x))))
(assert
  (forall ((p fun13) (x list2))
    (= (filter p x)
      (ite
        (is-cons2 x)
        (ite
          (apply13 p (head2 x)) (cons2 (head2 x) (filter p (tail2 x)))
          (filter p (tail2 x)))
        nil2))))
(assert
  (forall ((x Int) (y list3))
    (= (elem x y)
      (ite (is-cons3 y) (or (= x (head3 y)) (elem x (tail3 y))) false))))
(assert
  (forall ((x list2))
    (= (okay x)
      (ite
        (is-cons2 x)
        (and (not (elem (first (head2 x)) (map2 lam (tail2 x))))
          (okay (tail2 x)))
        true))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(assert
  (forall ((x Form) (y list2))
    (= (models x y)
      (ite
        (is-Var x)
        (ite
          (not (or2 (models4 (Var_0 x) y)))
          (cons (cons2 (Pair2 (Var_0 x) true) (filter (lam3 (Var_0 x)) y))
            nil)
          nil)
        (ite
          (is-Not x)
          (ite
            (is-Var (Not_0 x))
            (ite
              (not (or2 (models3 (Var_0 (Not_0 x)) y)))
              (cons
                (cons2 (Pair2 (Var_0 (Not_0 x)) false)
                  (filter (lam2 (Var_0 (Not_0 x))) y))
                nil)
              nil)
            (ite
              (is-Not (Not_0 x)) (models (Not_0 (Not_0 x)) y)
              (append (models (Not (&_0 (Not_0 x))) y)
                (models (& (&_0 (Not_0 x)) (Not (&_1 (Not_0 x)))) y))))
          (models2 (&_1 x) (models (&_0 x) y)))))))
(assert
  (forall ((q Form) (x list))
    (= (models2 q x)
      (ite (is-cons x) (models5 q (tail x) (models q (head x))) nil))))
(assert
  (forall ((q Form) (x list) (y list))
    (= (models5 q x y)
      (ite
        (is-cons y) (cons (head y) (models5 q x (tail y)))
        (models2 q x)))))
(assert
  (forall ((x fun1) (y list))
    (= (all x y)
      (ite
        (is-cons y) (and (apply1 x (head y)) (all x (tail y))) true))))
(assert (forall ((x2 Pair)) (= (apply12 lam x2) (fst x2))))
(assert
  (forall ((x2 Int) (x3 Pair))
    (= (apply13 (lam2 x2) x3) (distinct x2 (fst x3)))))
(assert
  (forall ((x4 Int) (x5 Pair))
    (= (apply13 (lam3 x4) x5) (distinct x4 (fst x5)))))
(assert (forall ((x list2)) (= (apply1 lam4 x) (okay x))))
(check-sat)
