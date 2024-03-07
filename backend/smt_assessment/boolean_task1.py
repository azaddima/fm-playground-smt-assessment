import sys
sys.path.append("..")  # Adds higher directory to python modules path.
from z3 import *


S = Solver()

S.from_file("./smtlib_examples//boolean_intro.smt2")
p, q, r = Bools('p q r')
formula = Not(Implies(p, Or(And(q, Not(r)), And(Not(q), r))))
S.add(formula)
#S.from_string("(assert (not (=> p (or (and q (not r)) (and (not q) r)))))")
if S.check() == unsat:
    print("correct evaluation of the task given")
else:
    print("Wrong conversion of xor statement")





