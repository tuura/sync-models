#!/usr/bin/env python

"""verilog_parser.py

A quick and dirty parser of a *subset* of the Verilog standard.

"""

import re
import json


def create_circuit():
    """Return a blank new circuit."""

    return { "name": None, "modules": [], "initial_state": {} }


def add_module(circuit, module_def):
    """Add a module defined in tuple 'module_def' to JSON object 'circuit'."""

    module = {
        "type": module_def[0],
        "instance": module_def[1],
        "connections": {}
    }

    if module["type"] == "module":

        # circuit definition
        circuit["name"] = module["instance"]

    else:

        # module instantiation
        con_reg = r".(?P<pin>\w+)[\s]*\([\s]*(?P<net>\w+)[\s]*\)[\s]*"
        con_str = module_def[2]
        matches = re.compile(con_reg).findall(con_str)

        for item in matches:
            pin, net = item
            module["connections"][pin] = net

        circuit["modules"].append(module)


def add_state(circuit, state_def):
    """Add circuit initial state information."""

    words = re.compile("([!\w]+)").findall(state_def)

    for item in words:

        if item[0] == "!":
            net, state = item[1:], 0
        else:
            net, state = item, 1

        circuit["initial_state"][net] = state


def add_inputs(circuit, inputs_def):

    nets = re.compile("(\w+)").findall(inputs_def)
    circuit["inputs"] = list(nets)


def add_outputs(circuit, outputs_def):

    nets = re.compile("(\w+)").findall(outputs_def)
    circuit["outputs"] = list(nets)


def load_verilog(file):

    # Read file content

    with open(file, "r") as fid:
        content = fid.read().replace("\r", "")

    # Generate a blank circuit

    circuit = create_circuit()

    # Define an array of 'mini_parsers'; tuples of (regex, func). All matches
    # of 'regex' are passed, alongside the current circuit definition, to
    # 'func' to update the circuit.

    # reg_module : matches the top module definition and module instantiations
    # reg_state  : matches the initial state comments generated by Workcraft
    # reg_inputs : matches input statements
    # reg_outputs : matches output statements

    reg_module = r"(?P<module>\w+)\s+(?P<instance>\w+)\s+\((?P<ports>[^;]+)\);"
    reg_state  = r"\/\/ signal values at the initial state:\s*\/\/\s*(.+)$"
    reg_inputs = r"\s*input\s+(.+);$"
    reg_outputs = r"\s*output\s+(.+);$"

    mini_parsers = [
        (reg_module, add_module),
        (reg_state,  add_state),
        (reg_inputs, add_inputs),
        (reg_outputs, add_outputs)
    ]

    # Parse and return result

    for reg, parse_ in mini_parsers:

        matches = re.compile(reg, flags=re.MULTILINE).findall(content)

        for item in matches:
            parse_(circuit, item)

    return circuit


def main():

    circuit = load_verilog("examples/d-element/circuit.v")

    print(json.dumps(circuit, indent=4))


if __name__ == '__main__':
    main()