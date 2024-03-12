import sys
sys.path.append("..")  # Adds higher directory to python modules path.
from z3 import *
import equivalence_encoding as enc

def evaluate_task1():

    student_encoding = parse_smt2_file("./smtlib_examples//boolean_intro.smt2")
    encoding_solution = parse_smt2_file("./solutions//boolean_intro.smt2")

    return enc.create_feedback(enc.comparison(student_encoding, encoding_solution), student_encoding, encoding_solution)

def evaluate_task2():

    student_encoding = parse_smt2_file("./smtlib_examples//mathematics.smt2")
    encoding_solution = parse_smt2_file("./solutions//mathematics.smt2")

    return enc.create_feedback(enc.comparison(student_encoding, encoding_solution), student_encoding, encoding_solution)

def evaluate_task3():

    student_encoding = parse_smt2_file("./smtlib_examples//mcqs.smt2")
    encoding_solution = parse_smt2_file("./solutions//mcqs.smt2")

    return enc.create_feedback(enc.comparison(student_encoding, encoding_solution), student_encoding, encoding_solution)

def evaluate_task4():

    student_encoding = parse_smt2_file("./smtlib_examples//knapsack.smt2")
    encoding_solution = parse_smt2_file("./solutions//knapsack.smt2")

    return enc.create_feedback(enc.comparison(student_encoding, encoding_solution), student_encoding, encoding_solution)

def evaluate_task5():

    student_encoding = parse_smt2_file("./smtlib_examples//decision_trees.smt2")
    encoding_solution = parse_smt2_file("./solutions//decision_trees.smt2")

    return enc.create_feedback(enc.comparison(student_encoding, encoding_solution), student_encoding, encoding_solution)

