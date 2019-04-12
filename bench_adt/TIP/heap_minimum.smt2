(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-datatypes () ((Maybe (Nothing) (Just (Just_0 Nat)))))
(declare-datatypes ()
  ((Heap (Node (Node_0 Heap) (Node_1 Nat) (Node_2 Heap)) (Nil))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun minimum (Heap) Maybe)
(declare-fun listMinimum (list) Maybe)
(declare-fun le (Nat Nat) Bool)
(declare-fun merge (Heap Heap) Heap)
(declare-fun toList (Nat Heap) list)
(declare-fun heapSize (Heap) Nat)
(declare-fun toList2 (Heap) list)
(assert
  (not
    (forall ((h Heap)) (= (listMinimum (toList2 h)) (minimum h)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
(assert
  (forall ((x Heap))
    (= (minimum x) (ite (is-Nil x) Nothing (Just (Node_1 x))))))
(assert
  (forall ((x list))
    (= (listMinimum x) (ite (is-cons x) (Just (head x)) Nothing))))
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
(check-sat)
