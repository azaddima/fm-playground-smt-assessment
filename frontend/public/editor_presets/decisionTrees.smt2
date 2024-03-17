;We have two similar decision trees, one is the pruned version of the other.
;Check if there are any cases in one decision tree that are not explored by the other
;(check if decision tree pruning covers the same cases )
(declare-const sex Bool) ; feature X[2]
(declare-const class Real) ; feature X[3]
(declare-const fare Real)
(declare-const age Real)

(declare-const classV1 Bool) ; clf2 in Python (depth 2)
(declare-const classV2 Bool) ; clf1 in Python (depth 3)


;original decision tree


;pruned decision tree
