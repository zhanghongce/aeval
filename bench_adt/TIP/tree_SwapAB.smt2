(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes ()
  ((Tree (Node (Node_0 Tree) (Node_1 Int) (Node_2 Tree)) (Nil))))
(declare-fun swap (Int Int Tree) Tree)
(declare-fun elem (Int list) Bool)
(declare-fun append (list list) list)
(declare-fun flatten0 (Tree) list)
(assert
  (not
    (forall ((p Tree) (a Int) (b Int))
      (=> (elem a (flatten0 p))
        (=> (elem b (flatten0 p))
          (and (elem a (flatten0 (swap a b p)))
            (elem b (flatten0 (swap a b p)))))))))
(assert
  (forall ((x Int) (y Int) (z Tree))
    (= (swap x y z)
      (ite
        (is-Nil z) Nil
        (ite
          (= (Node_1 z) x)
          (Node (swap x y (Node_0 z)) y (swap x y (Node_2 z)))
          (ite
            (= (Node_1 z) y)
            (Node (swap x y (Node_0 z)) x (swap x y (Node_2 z)))
            (Node (swap x y (Node_0 z)) (Node_1 z) (swap x y (Node_2 z)))))))))
(assert
  (forall ((x Int) (y list))
    (= (elem x y)
      (ite (is-cons y) (or (= x (head y)) (elem x (tail y))) false))))
(assert
  (forall ((x list) (y list))
    (= (append x y)
      (ite (is-cons x) (cons (head x) (append (tail x) y)) y))))
(assert
  (forall ((x Tree))
    (= (flatten0 x)
      (ite
        (is-Nil x) nil
        (append (append (flatten0 (Node_0 x)) (cons (Node_1 x) nil))
          (flatten0 (Node_2 x)))))))
(check-sat)
