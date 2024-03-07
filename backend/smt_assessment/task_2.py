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
if count == len(lst):
    print("correct evaluation of the given task.")

'''S.add(star == -1)
S.add(cloud == 495)
S.add(snowman == -136)
S.add(apple == -323)
S.add(secret == -186)
if S.check() == sat:
    print("correct evaluation of the task given")
else:
    print("Wrong conversion of xor statement")
'''

