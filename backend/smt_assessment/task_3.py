import sys
sys.path.append("..")  # Adds higher directory to python modules path.
from z3 import *


S = Solver()

S.from_file("./smtlib_examples//houses.smt2")
a, b, c, d, e, f = Bools('a b c d e f')
formulas = [a == And(b, c, d, e, f),
            b == And(Not(c), Not(d), Not(e), Not(f)),
            c == And(a, b),
            d == Or(And(a, Not(b), Not(c)), And(Not(a), b, Not(c)), And(Not(a), Not(b), c)),
            e == And(Not(a), Not(b), Not(c), Not(d)),
            f == And(Not(a), Not(b), Not(c), Not(d), Not(e))]
count = 0
i = 0
print(S)
for formula in formulas:
    S.push()
    S.add(Not(formula))
    if S.check() == unsat:
        count +=1
    else:
        print("Wrong conversion of the formula. formula " + str(i + 1) + " is wrong")
    i += 1

if(count == len(formulas)):
    print('correct evaluation of the formula')


