import sys
sys.path.append("..")  # Adds higher directory to python modules path.
from z3 import *


S = Solver()

S.from_file("./smtlib_examples//mathematics.smt2")
star, cloud, snowman, apple, secret = Ints('star cloud snowman apple secret')
lst = [star, cloud, snowman, apple, secret]
lstval = [-1, 495, -136,-323,-186]
count = 0
i = 0
for element in lst:
    S. add(element == lstval[i])
    if S.check() == sat:
        count += 1
    else:
        print("Wrong conversion of the formula. value of " + str(element) +" is wrong")
    i += 1
print(S)
if count == len(lst):
    print("correct evaluation of the given task.")

