(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-datatypes () ((Maybe (Nothing) (Just (Just_0 list)))))
(declare-datatypes ()
  ((Heap (Node (Node_0 Heap) (Node_1 Nat) (Node_2 Heap)) (Nil))))
(declare-datatypes () ((Maybe2 (Nothing2) (Just2 (Just_02 Heap)))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun listDeleteMinimum (list) Maybe)
(declare-fun le (Nat Nat) Bool)
(declare-fun merge (Heap Heap) Heap)
(declare-fun toList (Nat Heap) list)
(declare-fun heapSize (Heap) Nat)
(declare-fun toList2 (Heap) list)
(declare-fun maybeToList (Maybe2) Maybe)
(declare-fun deleteMinimum (Heap) Maybe2)
(assert
  (not
    (forall ((h Heap))
      (= (listDeleteMinimum (toList2 h))
        (maybeToList (deleteMinimum h))))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x list))
    (= (listDeleteMinimum x)
      (ite (is-cons x) (Just (tail x)) Nothing))))
(assert
  (forall ((x Nat) (y Nat))
    (= (le x y)
      (ite (is-S x) (ite (is-S y) (le (p x) (p y)) false) true))))
(assert
  (forall ((x Heap) (y Heap))
    (= (merge x y)
      (ite
        (is-Nil x) y
        (ite
          (is-Nil y) (Node (Node_0 x) (Node_1 x) (Node_2 x))
          (ite
            (le (Node_1 x) (Node_1 y))
            (Node (merge (Node_2 x) (Node (Node_0 y) (Node_1 y) (Node_2 y)))
              (Node_1 x) (Node_0 x))
            (Node (merge (Node (Node_0 x) (Node_1 x) (Node_2 x)) (Node_2 y))
              (Node_1 y) (Node_0 y))))))))
(assert
  (forall ((x Nat) (y Heap))
    (= (toList x y)
      (ite
        (is-S x)
        (ite
          (is-Nil y) nil
          (cons (Node_1 y) (toList (p x) (merge (Node_0 y) (Node_2 y)))))
        nil))))
(assert
  (forall ((x Heap))
    (= (heapSize x)
      (ite
        (is-Nil x) Z
        (S (plus (heapSize (Node_0 x)) (heapSize (Node_2 x))))))))
(assert
  (forall ((x Heap)) (= (toList2 x) (toList (heapSize x) x))))
(assert
  (forall ((x Maybe2))
    (= (maybeToList x)
      (ite (is-Just2 x) (Just (toList2 (Just_02 x))) Nothing))))
(assert
  (forall ((x Heap))
    (= (deleteMinimum x)
      (ite (is-Nil x) Nothing2 (Just2 (merge (Node_0 x) (Node_2 x)))))))
(check-sat)
