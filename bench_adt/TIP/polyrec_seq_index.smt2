(declare-sort sk_a 0)
(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(declare-datatypes (a b) ((Pair (Pair2 (first a) (second b)))))
(declare-datatypes (a) ((Maybe (Nothing) (Just (Just_0 a)))))
(declare-datatypes (a)
  ((Seq (Nil) (Cons (Cons_0 a) (Cons_1 (Seq (Pair a (Maybe a))))))))
(declare-fun (par (a b) (snd ((Pair a b)) b)))
(declare-fun (par (a) (pair ((list a)) (list (Pair a (Maybe a))))))
(declare-fun (par (a) (lookup (Int (list a)) (Maybe a))))
(declare-fun (par (a b) (fst ((Pair a b)) a)))
(declare-fun (par (a) (index (Int (Seq a)) (Maybe a))))
(declare-fun (par (a) (fromList ((list a)) (Seq a))))
(assert
  (not
    (forall ((n Int) (xs (list sk_a)))
      (=> (>= n 0) (= (lookup n xs) (index n (fromList xs)))))))
(assert
  (par (a b) (forall ((x (Pair a b))) (= (snd x) (second x)))))
(assert
  (par (a)
    (forall ((x (list a)))
      (= (pair x)
        (ite
          (is-cons x)
          (ite
            (is-cons (tail x))
            (cons (Pair2 (head x) (Just (head (tail x))))
              (pair (tail (tail x))))
            (cons (Pair2 (head x) (as Nothing (Maybe a)))
              (as nil (list (Pair a (Maybe a))))))
          (as nil (list (Pair a (Maybe a)))))))))
(assert
  (par (a)
    (forall ((x Int) (y (list a)))
      (= (lookup x y)
        (ite
          (is-cons y) (ite (= x 0) (Just (head y)) (lookup (- x 1) (tail y)))
          (as Nothing (Maybe a)))))))
(assert
  (par (a b) (forall ((x (Pair a b))) (= (fst x) (first x)))))
(assert
  (par (a)
    (forall ((x Int) (y (Seq a)))
      (= (index x y)
        (ite
          (is-Cons y)
          (ite
            (= x 0) (Just (Cons_0 y))
            (ite
              (= (mod x 2) 0)
              (let ((z (index (div (- x 1) 2) (Cons_1 y))))
                (ite (is-Just z) (snd (Just_0 z)) (as Nothing (Maybe a))))
              (let ((x2 (index (div (- x 1) 2) (Cons_1 y))))
                (ite
                  (is-Just x2) (Just (fst (Just_0 x2))) (as Nothing (Maybe a))))))
          (as Nothing (Maybe a)))))))
(assert
  (par (a)
    (forall ((x (list a)))
      (= (fromList x)
        (ite
          (is-cons x) (Cons (head x) (fromList (pair (tail x))))
          (as Nil (Seq a)))))))
(check-sat)
