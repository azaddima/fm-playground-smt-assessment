(declare-const sex Bool) ; feature X[2]
(declare-const class Real) ; feature X[3]
(declare-const fare Real)
(declare-const age Real)

(declare-const classV1 Int) ; clf2 in Python (depth 2)
(declare-const classV2 Int) ; clf1 in Python (depth 3)

;original decision tree
(assert (=> (and (= sex true) (<= class 2.5) (<= fare 32.0896)) (= classV1 1)))
(assert (=> (and (= sex true) (<= class 2.5) (> fare 32.0896)) (= classV1 1)))
(assert (=> (and (= sex true) (> class 2.5) (<= fare 23.0875)) (= classV1 1)))
(assert (=> (and (= sex true) (> class 2.5) (> fare 23.0875)) (= classV1 0)))
(assert (=> (and (= sex false) (<= class 1.5) (<= age 17.5)) (= classV1 1)))
(assert (=> (and (= sex false) (<= class 1.5) (> age 17.5)) (= classV1 0)))
(assert (=> (and (= sex false) (> class 1.5) (<= age 9.5)) (= classV1 0)))
(assert (=> (and (= sex false) (> class 1.5) (> age 9.5)) (= classV1 0)))

;pruned decision tree
(assert (=> (and (= sex true) (<= class 2.5)) (= classV1 1)))
(assert (=> (and (= sex true) (> class 2.5) (<= fare 23.0875)) (= classV1 1)))
(assert (=> (and (= sex true) (> class 2.5) (> fare 23.0875)) (= classV1 0)))
(assert (=> (and (= sex false) (<= class 1.5) (<= age 17.5)) (= classV1 1)))
(assert (=> (and (= sex false) (<= class 1.5) (> age 17.5)) (= classV1 0)))
(assert (=> (and (= sex false) (> class 1.5)) (= classV1 0)))
(assert (not (= classV1 classV2)))

(check-sat)
(get-model)