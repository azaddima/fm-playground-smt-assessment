from z3 import *


def run_z3(code: str):
    puzzle_input = smt2_example_parser('puzzle.smt2')

    solver = z3.Solver()
    solver.add(puzzle_input)
    print(solver)

    print(solver.to_smt2())

    return 'run z3'


def smt2_example_parser(filename: str):
    return parse_smt2_file('./smtlib_examples/' + filename)


# get model of smt2 file

# input2 = smt2_example_parser('puzzle.smt2')

# print(z3.Model(input2))

print(run_z3('puzzle.smt2'))
