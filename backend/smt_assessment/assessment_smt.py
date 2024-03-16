import pathlib
import subprocess
import sys
import tempfile

from equivalence_encoding import comparison

from equivalence_encoding import create_feedback

sys.path.append("..")  # Adds higher directory to python modules path.
from z3 import *
import json

debug = True


def run_assessment(user_input, task):
    """
    Run the assessment and returns feedback for the user.
    Args:
        user_input:
        task:
    Returns: feedback

    """

    # get solution filename
    solution_file = solution_path(task)

    s = Solver()

    # Create backtracking point to load only solution asserts
    s.push()
    s.from_file('./smt_assessment/solutions/' + solution_file)
    solution_asserts = s.assertions()
    s.pop()

    # Create backtracking point to load only user asserts
    s.push()
    user_asserts = parse_smt2_string(user_input)
    s.pop()

    # run the encoding
    comparison_data = comparison(user_asserts, solution_asserts)
    feedback = create_feedback(comparison_data, user_asserts, solution_asserts)

    return feedback


def solution_path(task):
    """
    Takes in task value and return the path of the solution file
    Args:
        task:

    Returns:
        file_path

    """
    with open('./smt_assessment/solutions/solution_files.json', 'r') as file:
        data = json.load(file)

    fileName = data[task]

    return fileName


if __name__ == '__main__':
    user_input = sys.argv[1]
    task = sys.argv[2]
    print(run_assessment(user_input, task))
