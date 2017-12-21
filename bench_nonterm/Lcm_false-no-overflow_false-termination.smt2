(declare-rel inv (Int Int Int Int))
(declare-var x Int)
(declare-var y Int)
(declare-var xm Int)
(declare-var xm1 Int)
(declare-var ym Int)
(declare-var ym1 Int)


(rule (inv x y x y))

(rule (=> 
    (and 
        (inv x y xm ym)
        (not (= xm ym))
        (= xm1 (ite (> xm ym) xm (+ xm x)))
        (= ym1 (ite (> xm ym) (+ ym y) ym))
    )
    (inv x y xm1 ym1)
  )
)
