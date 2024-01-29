import sys
sys.path.append("..")  # Adds higher directory to python modules path.
from z3 import *


S = Solver()
S.from_file("./smtlib_examples//boolean_intro.smt2")
S.from_string("(assert (not (=> p (or (and q (not r)) (and (not q) r)))))")
if S.check() == unsat:
    print("correct evaluation of the task given")
else:
    print("try again at line 6")


