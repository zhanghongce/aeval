(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))

(declare-fun tinsert (Tree Int) Tree)
(assert (forall ((i Int)) (= (tinsert leaf i) (node i leaf leaf))))
(assert (forall ((r Tree) (l Tree) (d Int) (i Int)) (= (tinsert (node d l r) i) (ite (< d i) (node d l (tinsert r i)) (node d (tinsert l i) r)))))

(declare-fun tinsert-all (Tree Lst) Tree)
(assert (forall ((x Tree)) (= (tinsert-all x nil) x)))
(assert (forall ((x Tree) (n Int) (l Lst)) (= (tinsert-all x (cons n l)) (tinsert (tinsert-all x l) n))))

(declare-fun tsize (Tree) Int)
(assert (= (tsize leaf) 0))
(assert (forall ((x Int) (l Tree) (r Tree)) (= (tsize (node x l r)) (+ 1 (+ (tsize l) (tsize r))))))

; extra lemmas
(assert (forall ((t Tree) (n Int)) (= (tsize (tinsert t n)) (+ 1 (tsize t)))))

(assert (not (forall ((l Lst) (t Tree)) (<= (tsize t) (tsize (tinsert-all t l))))))
(check-sat)
