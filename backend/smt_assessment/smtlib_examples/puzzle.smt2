;; Exercise 3 Task 2
;Encode the following Puzzle as a model for Z3
;(🍎 + ☁) + ⛄ = 36
;(⭐ + ⭐) * 🍎 = 646
;(⭐ * ⛄) - ⛄ = 272
;(🍎 - ⭐) - ⛄ = ?
(declare-const star Int)
(declare-const cloud Int)
(declare-const snowman Int)
(declare-const apple Int)
(declare-const secret Int)

(assert (= 36 (+ (+ cloud apple) snowman)))
(assert (= 646 (* (+ star star) apple)))
(assert (= 272 (- (* snowman star) snowman)))
(assert (= secret (- apple star snowman)))

(check-sat)
(get-model)
