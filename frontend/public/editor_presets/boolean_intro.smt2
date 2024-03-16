;make an encoding for the exclusive or operation using ands and ors
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
;(assert (and p q))
(assert (=> p (or (and q (not r)) (and (not q) r))))
(check-sat)
(get-model)



; translate an xor operation into smt:
; p implies q xor r
; hint: translate q xor r into propositional logic first

(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
;(assert (and p q))
(assert (=> p (or (and q (not r)) (and (not q) r))))
(check-sat)
(get-model)