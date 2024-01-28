;Introduce three new variables of type boolean
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
;assert p -> (q ^ !r) v (!q ^ r)
(assert (=> p (or (and q (not r) (and (not q) r)))))
(check-sat)
(get-model)