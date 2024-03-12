(declare-const ar Int)
(declare-const oud Int)
(declare-const owman Int)
(declare-const ple Int)
(declare-const cret Int)

(assert (= 36 (+ (+ oud ple) owman)))
(assert (= 646 (* (+ ar ar) ple)))
(assert (= 272 (- (* owman ar) owman)))
(assert (= cret (- ple ar owman)))

(check-sat)
(get-model)