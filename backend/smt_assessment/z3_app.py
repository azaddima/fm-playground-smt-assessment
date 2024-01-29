import sys

sys.path.append("..")  # Adds higher directory to python modules path.
from z3 import *


def run_assessment(input_code):
    code_input = parse_smt2_string(input_code)
    solver = z3.Solver()
    solver.add(code_input)
    output = solver.check()
    return str(output) + str(solver.model())


def smt2_example_parser(filename: str):
    """
        loads a smt2 file and returns an AstVector

        Parameters:
            filename (str): the filename of the smt2 file

        Returns:
            AstVector: array of the asserts
    """

    try:
        output = parse_smt2_file('./smtlib_examples/' + filename)
        return output
    except Exception as err:
        print(err)
        return err


if __name__ == '__main__':
    # Todo: remove
    for x in range(0, len(sys.argv)):
        print(str(x) + " " + sys.argv[x])

    code = sys.argv[1]
    print(run_assessment(code))
