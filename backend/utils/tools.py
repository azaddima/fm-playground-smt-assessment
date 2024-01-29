import os
import subprocess
import tempfile


def run_tool(code: str) -> str:
    """
     Run the code in z3 and return the output.

     Parameters:
       code (str): the code to run

     Returns:
       str: the output of the code if successful, otherwise the error or timeout message
     """

    # TODO: remove sample code
    code = sample_code

    tmp_file = tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.smt2')
    tmp_file.write(code.strip())
    tmp_file.close()

    result = print_formatted_feedback(str(run_assessment(code, tmp_file)))
    result += str(run_z3(code, tmp_file))

    os.remove(tmp_file.name)

    return result


def run_z3(code: str, tmp_file: tempfile) -> str:
    command = ["z3", "-smt2", tmp_file.name]
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=5)
        return result.stdout
    except subprocess.TimeoutExpired:
        return "Process timed out after {} seconds".format(5)


def run_assessment(code: str, tmp_file: tempfile) -> str:
    command = ["python3", './smt_assessment/assessment_smt.py', code]
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=5)
        return result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return "Process timed out after {} seconds".format(5)
    except subprocess.SubprocessError:
        return 'ERROR'


def print_formatted_feedback(message: str):
    return ("-------------------------------\n\n"
            "FEEDBACK:\n{}"
            "\n\n\n-------------------------------\n\n").format(message)


sample_code = """(set-option :produce-models true)
    (declare-const x Int)
    (declare-const y Int)
    (declare-const z Int)
    (assert (> x 1))
    (assert (> y 1))
    (assert (> (+ x y) 3))
    (assert (< (- z x) 10))
    (check-sat)
    (get-model)
    """

print(run_tool('ho'))
