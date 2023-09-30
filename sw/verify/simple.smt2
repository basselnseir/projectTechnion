(set-logic HORN)
; benchmark generated from python API
(set-info :status unknown)
(declare-fun inv (Int Int Int Int) Bool)
(assert
 (forall ((b Int) (a Int) )(let (($x283 (inv a b a 0)))
 (let (($x390 (> b 0)))
 (let (($x333 (and $x390)))
 (=> $x333 $x283)))))
 )
(assert
 (forall ((a Int) (b Int) (x Int) (y Int) )(let (($x564 (inv a b (+ x 1) (+ y 1))))
 (let (($x442 (inv a b x y)))
 (let (($x284 (and $x442 (< y b))))
 (=> $x284 $x564)))))
 )
(assert
 (forall ((a Int) (b Int) (x Int) (y Int) )(let (($x442 (inv a b x y)))
 (let (($x384 (and $x442 (>= y b) (not (= x (+ a b))))))
 (=> $x384 false))))
 )
(check-sat)
