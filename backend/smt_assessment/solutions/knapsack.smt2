(declare-const box1num Int)
(declare-const box2num Int)
(declare-const box3num Int)

(declare-const totalnum Int)
(declare-const totalcost Int)

(assert (= totalnum (+ box1num (* 3 box2num) (* 5 box3num))))
(assert (= totalcost (+ box1num (* 2 box2num) (* 3 box3num))))

(assert(>= box1num 0))
(assert(>= box2num 0))
(assert(>= box3num 0))

(assert(<= totalcost 8))

(maximize totalnum)

(check-sat)
(get-model)