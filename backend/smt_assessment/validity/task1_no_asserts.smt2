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

(check-sat)
(get-model)