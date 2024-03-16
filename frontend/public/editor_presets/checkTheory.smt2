;Check if this theory holds true: ((x xor y) or z) =((x or z ) xor (y or z))
(assert
    (forall ((x Bool) (y Bool) (z Bool))
        (=
            (or (xor x y) z)
            (xor (or x z) (or y z)))))

(check-sat)
