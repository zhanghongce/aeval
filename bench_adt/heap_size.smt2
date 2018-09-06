(declare-datatypes () ((Heap (hleaf) (heap (rk Int) (value Int) (hleft Heap) (hright Heap)))))

(declare-fun hsize (Heap) Int)
(assert (= (hsize hleaf) 0))
(assert (forall ((k Int) (v Int) (l Heap) (r Heap)) (= (hsize (heap k v l r)) (+ 1 (+ (hsize l) (hsize r))))))

(assert (not (forall ((x Heap)) (>= (hsize x) 0))))
(check-sat)
