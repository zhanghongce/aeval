(declare-datatypes () ((list (nil) (cons (head Int) (tail list)))))
(declare-datatypes () ((Pair (Pair2 (first Bool) (second list)))))
(declare-fun ordered (list) Bool)
(declare-fun bubble (list) Pair)
(declare-fun bubsort (list) list)
(assert (not (forall ((x list)) (ordered (bubsort x)))))
(assert
  (forall ((x list))
    (= (ordered x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (and (<= (head x) (head (tail x)))
            (ordered (cons (head (tail x)) (tail (tail x)))))
          true)
        true))))
(assert
  (forall ((x list))
    (= (bubble x)
      (ite
        (is-cons x)
        (ite
          (is-cons (tail x))
          (ite
            (<= (head x) (head (tail x)))
            (let ((y (bubble (cons (head (tail x)) (tail (tail x))))))
              (Pair2 (first y) (cons (head x) (second y))))
            (Pair2 true
              (cons (head (tail x))
                (second (bubble (cons (head x) (tail (tail x))))))))
          (Pair2 false (cons (head x) nil)))
        (Pair2 false nil)))))
(assert
  (forall ((x list))
    (= (bubsort x)
      (let ((y (bubble x))) (ite (first y) (bubsort (second y)) x)))))
(check-sat)
