(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))

(declare-fun tsize (Tree) Int)
(assert (= (tsize leaf) 0))
(assert (forall ((x Int) (l Tree) (r Tree)) (= (tsize (node x l r)) (+ 1 (+ (tsize l) (tsize r))))))

(assert (not (forall ((x Tree)) (>= (tsize x) 0))))
(check-sat)
