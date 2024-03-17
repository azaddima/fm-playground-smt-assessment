;A certain question has the following possible answers.
;a. All of the below
;b. None of the below
;c. All of the above
;d. One of the above
;e. None of the above
;f. None of the above
;Which answer is correct?.


( declare-const a Bool )
( declare-const b Bool )
( declare-const c Bool )
( declare-const d Bool )
( declare-const e Bool )
( declare-const f Bool )

(assert (= c (and a b)))
(assert (= a (and b c d e f)))
(assert (= b (and (not c) (not d) (not e) (not f))))
(assert (= d (or (and a (not b) (not c)) (and (not a) b (not c))(and (not a) (not b) c))))
(assert (= e (and (not a) (not b) (not c) (not d))))
(assert (= f (and (not a) (not b) (not c) (not d) (not e))))

(check-sat)
(get-model)