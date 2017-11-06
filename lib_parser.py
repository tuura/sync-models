

import re


def make_int_lambda(boolean_lambda):

    def int_lambda(**args):
        bool_args = { key: bool(val) for key, val in args.iteritems() }
        bool_result = boolean_lambda(**bool_args)
        int_result = 1 if bool_result else 0
        return int_result

    return int_lambda


def get_lambda(gate_def, inputs):
    """Return a Python lambda from a lib gate definition and set of inputs."""

    _, expr = gate_def.split("=")

    rlist = [
        ("*", " and "),
        ("+", " or "),
        ("!", "not "),
        ("CONST0", "False"),
        ("CONST1", "True"),
    ]

    for item in rlist:
        expr = expr.replace(*item)

    input_str = ", ".join(inputs)

    lambda_str = "lambda %s: %s" % (input_str, expr)

    boolean_lambda = eval(lambda_str)

    return make_int_lambda(boolean_lambda)


def parse_gate_def(gate_type, gate_name, gate_def, dummy=None, state_input=None):

    constants = { "CONST0", "CONST1" }

    reg_signals = r"[\w0-9]+"

    signals = re.compile(reg_signals, flags=re.MULTILINE).findall(gate_def)

    output, inputs = signals[0], set(signals[1:]) - constants

    return {
        "type": gate_type,
        "state_input": state_input,
        "name": gate_name,
        "output": output,
        "inputs": inputs,
        "definition": gate_def,
        "lambda": get_lambda(gate_def, inputs),
    }


def load_lib(file):

    with open(file, "r") as fid:
        content = fid.read().replace("\r", "")

    reg_gate = r"^(GATE|LATCH)\s*(\w+)\s*[0-9]+\s*([\w=!()\*+]+);([\w.\s]+SEQ\s+[\w]+\s+(\w+))?";

    matches = re.compile(reg_gate, flags=re.MULTILINE).findall(content)

    lib = { item[1]: parse_gate_def(*item) for item in matches }

    return lib


def main():

    file = "libraries/workcraft.lib"

    lib = load_lib(file)

    print lib["AND2"]


if __name__ == '__main__':
    main()
