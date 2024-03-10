import sys
sys.path.append("..")  # Adds higher directory to python modules path.
from z3 import *


S = Solver()
userFormulas = parse_smt2_file("./smtlib_examples//decisionTrees.smt2")

print(userFormulas)

teacherFormulas = parse_smt2_file("./smtlib_examples//teacher_answer.smt2")
count = 0
i = 0
for formula in userFormulas:

    S.push()
    S.add(Not(teacherFormulas[i] == formula))
    if S.check() == unsat:
        count +=1
    else:
        print("Wrong conversion of the formula. formula " + str(formula.s) + " is wrong")
    i += 1
    S.pop()

if(count == len(userFormulas)):
    print('correct evaluation of the formula')
