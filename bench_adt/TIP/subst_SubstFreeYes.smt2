(declare-sort fun1 0)
(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes ()
  ((Expr (Var (Var_0 Int))
     (Lam (Lam_0 Int) (Lam_1 Expr)) (App (App_0 Expr) (App_1 Expr)))))
(declare-fun lam (Int) fun1)
(declare-fun lam2 (Int) fun1)
(declare-fun apply1 (fun1 Int) Bool)
(declare-fun new_maximum (Int list) Int)
(declare-fun new (list) Int)
(declare-fun filter (fun1 list) list)
(declare-fun elem (Int list) Bool)
(declare-fun append (list list) list)
(declare-fun free (Expr) list)
(declare-fun subst (Int Expr Expr) Expr)
(assert
  (not
    (forall ((x Int) (e Expr) (a Expr) (y Int))
      (=> (elem x (free a))
        (= (elem y (append (filter (lam2 x) (free a)) (free e)))
          (elem y (free (subst x e a))))))))
(assert
  (forall ((x Int) (y list))
    (= (new_maximum x y)
      (ite
        (is-cons y)
        (ite
          (<= x (head y)) (new_maximum (head y) (tail y))
          (new_maximum x (tail y)))
        x))))
(assert (forall ((x list)) (= (new x) (+ (new_maximum 0 x) 1))))
(assert
  (forall ((p fun1) (x list))
    (= (filter p x)
      (ite
        (is-cons x)
        (ite
          (apply1 p (head x)) (cons (head x) (filter p (tail x)))
          (filter p (tail x)))
        nil))))
(assert
  (forall ((x Int) (y list))
    (= (elem x y)
      (ite (is-cons y) (or (= x (head y)) (elem x (tail y))) false))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(assert
  (forall ((x Expr))
    (= (free x)
      (ite
        (is-App x) (append (free (App_0 x)) (free (App_1 x)))
        (ite
          (is-Lam x) (filter (lam (Lam_0 x)) (free (Lam_1 x)))
          (cons (Var_0 x) nil))))))
(assert
  (forall ((x Int) (y Expr) (z Expr))
    (= (subst x y z)
      (ite
        (is-App z) (App (subst x y (App_0 z)) (subst x y (App_1 z)))
        (ite
          (is-Lam z)
          (let ((z2 (new (append (free y) (free (Lam_1 z))))))
            (ite
              (= x (Lam_0 z)) (Lam (Lam_0 z) (Lam_1 z))
              (ite
                (elem (Lam_0 z) (free y))
                (subst x y (Lam z2 (subst (Lam_0 z) (Var z2) (Lam_1 z))))
                (Lam (Lam_0 z) (subst x y (Lam_1 z))))))
          (ite (= x (Var_0 z)) y (Var (Var_0 z))))))))
(assert
  (forall ((z Int) (x2 Int))
    (= (apply1 (lam z) x2) (distinct z x2))))
(assert
  (forall ((x Int) (z Int)) (= (apply1 (lam2 x) z) (distinct z x))))
(check-sat)
