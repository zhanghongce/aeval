(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes ()
  ((Tree (TNode (TNode_0 Tree) (TNode_1 Int) (TNode_2 Tree))
     (TNil))))
(declare-fun null (list) Bool)
(declare-fun flatten (Tree list) list)
(declare-fun elem (Int list) Bool)
(declare-fun delete (Int list) list)
(declare-fun isPermutation (list list) Bool)
(declare-fun add (Int Tree) Tree)
(declare-fun toTree (list) Tree)
(declare-fun tsort (list) list)
(assert (not (forall ((x list)) (isPermutation (tsort x) x))))
(assert (forall ((x list)) (= (null x) (not (is-cons x)))))
(assert
  (forall ((x Tree) (y list))
    (= (flatten x y)
      (ite
        (is-TNil x) y
        (flatten (TNode_0 x)
          (cons (TNode_1 x) (flatten (TNode_2 x) y)))))))
(assert
  (forall ((x Int) (y list))
    (= (elem x y)
      (ite (is-cons y) (or (= x (head y)) (elem x (tail y))) false))))
(assert
  (forall ((x Int) (y list))
    (= (delete x y)
      (ite
        (is-cons y)
        (ite (= x (head y)) (tail y) (cons (head y) (delete x (tail y))))
        nil))))
(assert
  (forall ((x list) (y list))
    (= (isPermutation x y)
      (ite
        (is-cons x)
        (and (elem (head x) y)
          (isPermutation (tail x) (delete (head x) y)))
        (null y)))))
(assert
  (forall ((x Int) (y Tree))
    (= (add x y)
      (ite
        (is-TNil y) (TNode TNil x TNil)
        (ite
          (<= x (TNode_1 y))
          (TNode (add x (TNode_0 y)) (TNode_1 y) (TNode_2 y))
          (TNode (TNode_0 y) (TNode_1 y) (add x (TNode_2 y))))))))
(assert
  (forall ((x list))
    (= (toTree x)
      (ite (is-cons x) (add (head x) (toTree (tail x))) TNil))))
(assert (forall ((x list)) (= (tsort x) (flatten (toTree x) nil))))
(check-sat)
