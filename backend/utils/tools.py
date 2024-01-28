import os
import subprocess
import tempfile

from backend.smt_assessment.z3_app import run_z3


# import z3_app.py

def run_tool(code: str) -> str:
    """
     Run the code in z3 and return the output.

     Parameters:
       code (str): the code to run

     Returns:
       str: the output of the code if successful, otherwise the error or timeout message

     TODO (maybe): Logging the resource usage of the subprocess. Windows: psutil, Linux: resource.getrusage(resource.RUSAGE_CHILDREN)
     """
    tmp_file = tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.smt2')
    tmp_file.write(code.strip())
    tmp_file.close()
    command = ["z3", "-smt2", tmp_file.name]
    try:
        result = subprocess.run(command, capture_output=True, text=True, timeout=5)
        os.remove(tmp_file.name)

        return (("-------------------------------\n\n"
                 "Feedback: "
                 "\nInput is not the same as solution\n\n-------------------------------\n\n")
                + result.stdout)
    except subprocess.TimeoutExpired:
        os.remove(tmp_file.name)
        return "Process timed out after {} seconds".format(5)
