import sys
sys.path.append("..")  # Adds higher directory to python modules path.
from z3 import *
import equivalence_encoding as enc

#Evaluating each task presented to the user
def evaluate_task1():

    student_encoding = parse_smt2_file("./validity//task1_all_correct.smt2")
    encoding_solution = parse_smt2_file("./solutions//mcqs.smt2")

    if "CORRECT SOLUTION" in enc.create_feedback(enc.comparison(student_encoding, encoding_solution),
                                                 student_encoding, encoding_solution):
        return "Test-> All asserts are correct: passed"
    else:
        return "Test-> All asserts are correct: failed"

def evaluate_task2():

    student_encoding = parse_smt2_file("./validity//task1_all_correct_reordered.smt2")
    encoding_solution = parse_smt2_file("./solutions//mcqs.smt2")

    if "CORRECT SOLUTION" in enc.create_feedback(enc.comparison(student_encoding, encoding_solution),
                                                   student_encoding, encoding_solution):
        return "Test-> Asserts have a changed order: passed"
    else:
        return "Test-> Asserts have a changed order: failed"

def evaluate_task3():

    student_encoding = parse_smt2_file("./validity//task1_all_wrong.smt2")
    encoding_solution = parse_smt2_file("./solutions//mcqs.smt2")

    if "INCORRECT SOLUTION" in enc.create_feedback(enc.comparison(student_encoding, encoding_solution),
                                                   student_encoding, encoding_solution):
        return "Test-> All asserts are wrong: passed"
    else:
        return "Test-> All asserts are wrong: failed"

def evaluate_task4():

    student_encoding = parse_smt2_file("./validity//task1_partially_wrong.smt2")
    encoding_solution = parse_smt2_file("./solutions//mcqs.smt2")

    if "INCORRECT SOLUTION" in enc.create_feedback(enc.comparison(student_encoding, encoding_solution),
                                                   student_encoding, encoding_solution):
        return "Test-> Some asserts are wrong: passed"
    else:
        return "Test-> Some asserts are wrong: failed"

def evaluate_task5():

    student_encoding = parse_smt2_file("./validity//task1_no_asserts.smt2")
    encoding_solution = parse_smt2_file("./solutions//mcqs.smt2")

    if "INCORRECT SOLUTION" in enc.create_feedback(enc.comparison(student_encoding, encoding_solution), student_encoding, encoding_solution):

        return "Test-> No asserts are present: passed"
    else:
        return "Test-> No asserts are present: failed"


if __name__== "__main__":
    print(evaluate_task1())
    print(evaluate_task2())
    print(evaluate_task3())
    print(evaluate_task4())
    print(evaluate_task5())