;
;
;
;
(assert
    (forall ((x Bool) (y Bool) (z Bool))
        (=
            (or (xor x y) z)
            (xor (or x z) (or y z)))))

(check-sat)
