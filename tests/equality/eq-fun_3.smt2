(assert (= a1 b1))
(assert (= a2 b2))
(assert (= a3 b3))
(assert (not (= (f a1 a2 a3) (f b1 b2 b3))))
(check-sat)
