#!/usr/bin/env python

"""verilog_parser.py

A quick and dirty parser of a *subset* of the Verilog standard.

"""

import re
import json


def create_circuit():
    """Return a blank new circuit."""

    return { "name": None, "modules": [] }


def add_module(circuit, module_def):
    """Add a module defined in tuple 'module_def' to JSON object 'circuit'."""

    module = {
        "type": module_def[0],
        "instance": module_def[1],
        "connections": []
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
            module["connections"].append({ "pin": item[0], "net": item[1] })

        circuit["modules"].append(module)


def parse(file):

    # Read file content

    with open(file, "r") as fid:
        content = fid.read()

    # Generate a blank circuit

    circuit = create_circuit()

    # Define an array of 'mini_parsers'; tuples of (regex, func). All matches
    # of 'regex' are passed, alongside the current circuit definition, to
    # 'func' to update the circuit.

    reg_module = r"(?P<module>\w+)\s+(?P<instance>\w+)\s+\((?P<ports>[^;]+)\);"

    mini_parsers = [
        (reg_module, add_module)
    ]

    # Parse and return result

    for reg, parse_ in mini_parsers:

        matches = re.compile(reg).findall(content)

        for item in matches:
            parse_(circuit, item)

    return circuit


def main():

    circuit = parse("examples/d-element/circuit.v")

    print(json.dumps(circuit, indent=4))


if __name__ == '__main__':
    main()