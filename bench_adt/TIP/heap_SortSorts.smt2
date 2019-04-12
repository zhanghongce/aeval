(declare-datatypes () ((Nat (Z) (S (p Nat)))))
(declare-datatypes () ((list (nil) (cons (head Nat) (tail list)))))
(declare-datatypes ()
  ((Heap (Node (Node_0 Heap) (Node_1 Nat) (Node_2 Heap)) (Nil))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun le (Nat Nat) Bool)
(declare-fun merge (Heap Heap) Heap)
(declare-fun toList (Nat Heap) list)
(declare-fun ordered (list) Bool)
(declare-fun insert2 (Nat Heap) Heap)
(declare-fun toHeap (list) Heap)
(declare-fun heapSize (Heap) Nat)
(declare-fun toList2 (Heap) list)
(declare-fun hsort (list) list)
(assert (not (forall ((x list)) (ordered (hsort x)))))
(assert
  (forall ((x Nat) (y Nat))
    (= (plus x y) (ite (is-S x) (S (plus (p x) y)) y))))
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
  (forall ((x list))
    (= (ordered x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (and (le (head x) (head (tail x)))
            (ordered (cons (head (tail x)) (tail (tail x)))))
          true)
        true))))
(assert
  (forall ((x Nat) (y Heap))
    (= (insert2 x y) (merge (Node Nil x Nil) y))))
(assert
  (forall ((x list))
    (= (toHeap x)
      (ite (is-cons x) (insert2 (head x) (toHeap (tail x))) Nil))))
(assert
  (forall ((x Heap))
    (= (heapSize x)
      (ite
        (is-Nil x) Z
        (S (plus (heapSize (Node_0 x)) (heapSize (Node_2 x))))))))
(assert
  (forall ((x Heap)) (= (toList2 x) (toList (heapSize x) x))))
(assert (forall ((x list)) (= (hsort x) (toList2 (toHeap x)))))
(check-sat)
