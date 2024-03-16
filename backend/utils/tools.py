import os
import subprocess
import tempfile


def run_tool(user_input: str) -> str:
    """
     Run the code in z3 and return the output.

     Parameters:
       user_input (str): the user input to assess against the solution

     Returns:
       str: the output of the code if successful, otherwise the error or timeout message
     """

    # Load current task value which was temporarily added at the beginning of the string
    current_task = user_input[0]
    # Remove the task value from input string
    user_input = user_input[1:]

    tmp_file = tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.smt2')
    tmp_file.write(user_input.strip())
    tmp_file.close()

    result = print_formatted_feedback(str(run_assessment(user_input, current_task)))
    result += str(run_z3(tmp_file))

    os.remove(tmp_file.name)

    return result


def run_z3(tmp_file: tempfile) -> str:
    command = ["z3", "-smt2", tmp_file.name]
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=5)
        return result.stdout
    except subprocess.TimeoutExpired:
        return "Process timed out after {} seconds".format(5)


def run_assessment(user_input: str, task_index: str) -> str:
    command = ["python3", 'smt_assessment/assessment_smt.py', user_input, task_index]
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
