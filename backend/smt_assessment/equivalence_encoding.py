import sys

sys.path.append("..")  # Adds higher directory to python modules path.
from z3 import *


# TODO: compare  with the test from the lecture assignments
# TODO: read into the Solver context ctx parameter
# TODO: find a way to extract the asserts into a list

def check_equivalence(input_expr, reference_expr) -> CheckSatResult:
    """
    Check if two asserts are equivalent, and return CheckSatResult.
    Equality is given if unsat is returned.
    """

    s = Solver()
    s.push()

    # Convert asserts lists intro CNF and assert disequation (negation of equation)
    s.add(And(input_expr) != And(reference_expr))
    check_sat = s.check()
    s.pop()

    return check_sat


def check_entailment(input_assert, reference_asserts):
    """
    Check entailment and return CheckSatResult
    """

    s = Solver()
    s.push()

    s.add(reference_asserts)
    s.add(Not(input_assert))
    check_sat = s.check()

    s.pop()

    return check_sat


def combinations(items, n, start=0, current=[]):
    """Generate combinations of 'n' items chosen from a list.

  Args:
      items: The list of items.
      n: The length of each combination.
      start: The starting index for choosing items (default 0).
      current: The current partially built combination (default empty list).
  """
    if n == 0:
        return [list(current)]  # Return a copy of the complete combination
    else:
        result = []
        for i in range(start, len(items)):
            current.append(items[i])
            result += combinations(items, n - 1, i + 1,
                                   current.copy())  # Use current.copy()
            current.pop()
        return result


def comparison(input_asserts, reference_asserts: list):
    """Compare the input and reference asserts and return a feedback string
    
    Args:
        input_asserts: list of input asserts
        reference_asserts: list of reference asserts
    Returns: 
        feedback: string with feedback for the user
    """

    # TODO: initial check if solution is wholey equal to the reference solution

    # Create int indices for input and reference asserts for easier computation
    input_indices = list(range(len(input_asserts)))
    reference_indices = list(range(len(reference_asserts)))

    # We want to remove the input asserts that are not entailed by the reference asserts and vice versa
    # Check for entailment of input asserts and remove non-valid asserts
    for i in range(len(input_indices)):
        # sat means that the input assert is not entailed by the reference
        if check_entailment(input_asserts[i], reference_asserts) == sat:
            input_indices.remove(i)

    for i in range(len(reference_indices)):
        if check_entailment(reference_asserts[i], input_asserts) == sat:
            reference_indices.remove(i)

    # save the indices of the input and reference asserts that are are entailed by the other
    valid_input_indices = input_indices
    valid_reference_indices = reference_indices

    # Generate all possible combinations of input indices for given length
    # and compare with all combinations of reference indices
    equal_asserts = []

    process_finished = False
    combinations_length = 0
    restart = False
    while not process_finished:

        if restart:
            restart = False
        else:
            # Only increase combination length,
            # if there are still valid indices left after current combination length
            combinations_length += 1

        # Generate all possible combinations of input indices for given length
        input_combos = combinations(input_indices, combinations_length)
        # print(input_combos)

        # Compare with all combinations of reference asserts
        for input_combo in input_combos:
            if restart:
                break

            # Compare with all combinations of reference indices
            for j in range(len(reference_indices)):
                if restart:
                    break

                reference_combos = combinations(reference_indices, j + 1)

                for reference_combo in reference_combos:

                    # check if the input and reference combo are equivalent
                    # if they are, remove the input and reference indices from the valid indices
                    # if they are not, continue to the next combination
                    check_sat = check_equivalence(
                        [input_asserts[i] for i in input_combo],
                        [reference_asserts[i] for i in reference_combo],
                    )

                    if check_sat == unsat:
                        # print(input_combo)
                        for i in range(len(input_combo)):
                            input_indices.remove(input_combo[i])
                        for i in range(len(reference_combo)):
                            reference_indices.remove(reference_combo[i])

                        # save the indices of the combinations input and reference asserts that are equal
                        equal_asserts.append([input_combo, reference_combo])

                        restart = True
                        break

        if combinations_length == len(input_indices):
            process_finished = True

    data = {
        "valid_input_indices": valid_input_indices,
        "valid_reference_indices": valid_reference_indices,
        'equal_asserts': equal_asserts,
    }

    return data


def create_feedback(comparison_data, input_asserts, reference_asserts):
    """Create feedback string from comparison data
    
    Args:
        comparison_data: dictionary with comparison data
    Returns: 
        feedback: string with feedback for the user
    """

    feedback = "The following asserts are entailed by the reference asserts: \n"
    for index in comparison_data["valid_input_indices"]:
        feedback += f"{index}: {input_asserts[index]}\n"

    feedback += "The following asserts are equivalent: \n"
    for assert_pair in comparison_data['equal_asserts']:
        feedback += f"Input asserts: {[input_asserts[user_assert] for user_assert in assert_pair[0]]}\n"
        feedback += f"Reference asserts: {[reference_asserts[reference_assert] for reference_assert in assert_pair[1]]}\n"

    return feedback


if __name__ == '__main__':
    # Define solver with new Context()

    # working_Context = Context()
    s = Solver()

    # get list of the asserts
    s.push()
    s.from_file("./smtlib_examples/houses.smt2")
    user_asserts = s.assertions()
    s.pop()

    ### SOLUTION
    a, b, c, d, e, f = Bools('a b c d e f')
    formulas = [
        a == And(b, c, d, e, f),
        b == And(Not(c), Not(d), Not(e), Not(f)),
        c == And(a, b),
        d == Or(And(a, Not(b), Not(c)), And(Not(a), b, Not(c)),
                And(Not(a), Not(b), c)),
        e == And(Not(a), Not(b), Not(c), Not(d)),
        f == And(Not(a), Not(b), Not(c), Not(d), Not(e)),
    ]

    # TEST FORMULAS
    formulas_test = [
        a == And(a, b, c),
        a == And(b, c, d, e, f),
        a == And(d, e, f),
        b == And(Not(c), Not(d), Not(e), Not(f)),
    ]

    comparison_data = comparison(formulas_test, formulas)

    print(comparison_data['equal_asserts'])

    print('Printing correct asserts ....')
    for asserts in comparison_data['equal_asserts']:
        for index in asserts[0]:
            print(formulas_test[index])

    print('Printing asserts which are entailed by the solution ....')
