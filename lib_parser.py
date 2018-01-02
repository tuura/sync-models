import re
import json
import glob


def make_int_lambda(boolean_lambda):

    def int_lambda(**args):
        bool_args = {key: bool(val) for key, val in args.iteritems()}
        bool_result = boolean_lambda(**bool_args)
        int_result = 1 if bool_result else 0
        return int_result

    return int_lambda


def merge_libs(*libs):
    """Merge a list of libraries."""

    merged = dict()

    for lib in libs:
        merged.update(lib)

    return merged


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


def parse_gate_def(gate_type, gate_name, gate_def, dummy=None,
                   state_input=None):

    constants = {"CONST0", "CONST1"}

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


def load_lib(*files):
    """Load and return multiple libraries as one.

    'files' items can be glob patterns (e.g. 'libraries/*.lib').
    """

    matches = [glob.glob(file) for file in files]
    matches_flat = sum(matches, [])

    libs = map(load_single_lib, matches_flat)
    return merge_libs(*libs)


def load_single_lib(file):

    with open(file, "r") as fid:
        content = fid.read().replace("\r", "")

    reg_gate = r"^(GATE|LATCH)\s*(\w+)\s*[0-9]+" + \
        r"\s*([\w=!()\*+]+);([\w.\s]+SEQ\s+[\w]+\s+(\w+))?"

    matches = re.compile(reg_gate, flags=re.MULTILINE).findall(content)

    lib = {item[1]: parse_gate_def(*item) for item in matches}

    return lib


def write_file(file, content):
    with open(file, "w") as fid:
        fid.write(content)


def export_verilog(lib, output_file):
    """Export library as verilog file."""

    def get_verilog_expr(lib_expr):
        """Return the verilog equivalent of a lib experession, for example:
        'y=!(A*B+C)' -> 'y=~(A&B|C)'.
        """
        reps = [("!", "~"), ("*", " & "), ("+", " | "), ("=", " = "),
                ("CONST", "")]

        def red_fun(expr, item):
            return expr.replace(*item)

        return reduce(red_fun, reps, lib_expr)

    def get_module_verilog(mod_tup):
        """Return verilog representation of module."""
        name, module = mod_tup
        output_port_parts = ["output %s" % module["output"]]
        input_port_parts = ["input %s" % input for input in module["inputs"]]
        port_parts = output_port_parts + input_port_parts
        port_str = ", ".join(port_parts)
        header = "module %s (%s);" % (name, port_str)
        body = "    assign %s;" % get_verilog_expr(module["definition"])
        footer = "endmodule"
        return "\n".join([header, body, footer])

    gates = filter(lambda item: item[1]["type"] == "GATE", lib.iteritems())
    mod_strs = map(get_module_verilog, gates)
    verilog_str = "\n\n".join(mod_strs)
    write_file(output_file, verilog_str)


def main():
    lib = load_lib("libraries/workcraft.lib")
    export_verilog(lib, "gates/workcraft.v")


if __name__ == '__main__':
    main()
