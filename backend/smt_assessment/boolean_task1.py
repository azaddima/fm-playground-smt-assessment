import sys
sys.path.append("..")  # Adds higher directory to python modules path.
from z3 import *

p, q, r = Bools('p, q, r')
S = Solver()
f = parse_smt2_file("smtlib_examples//boolean_intro.smt2")
f_bool = BoolVector( f,  len(f))
print(f_bool)
p, q, r = Bools('p, q, r')
check_f = Implies(p, Or(And(q, Not(r), And(Not(q), r))))

S.add(f)
new_from_front = Bool(obj_to_string(f)) == check_f




S.add(Not(new_from_front))

if S.check() == unsat:
    print("correct evaluation of the task given")
else:
    print( "try again at line 6")


#[Implies(p, Or(And(q, Not(r), And(Not(q), r))))]




