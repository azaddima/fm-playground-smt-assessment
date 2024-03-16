;solve this numeric problem (find the value of e)
;(d + b) + c = 36
;(a + a) * d = 646
;(a * c) - c = 272
;(d - a) - c = e


(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e Int)

(assert (= 36 (+ (+ b d)  c)))
(assert (= 646 (* (+ a a) d)))
(assert (= 272 (- (*  c a)  c)))
(assert (= e (- d a  c)))

(check-sat)
(get-model)