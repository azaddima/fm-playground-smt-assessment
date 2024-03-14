;make an encoding for the exclusive or operation using ands and ors
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
;assert p -> (q ^ !r) v (!q ^ r)
(assert (=> p (or (and q (not r)) (and (not q) r))))
(check-sat)
(get-model)