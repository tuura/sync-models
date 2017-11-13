#!/usr/bin/env python

from math import ceil
from math import log
from jinja2 import Template
from sg_parser import load_sg
from lib_parser import load_lib
from collections import defaultdict
from verilog_parser import load_verilog

import os
import json


def read_file(file):
    """Return content of file as a string."""
    with open(file, "r") as fid:
        return fid.read()


def write_file(content, file):
    """Write string 'content' to file."""
    with open(file, "w") as fid:
        fid.write(content)


def get_state_inds(spec):
    """Returns a map: state -> unique index."""
    froms = [ item[0] for item in spec["transitions"]]
    tos   = [ item[1] for item in spec["transitions"]]
    states = sorted(set(froms + tos))
    inds = { state: ind for ind, state in enumerate(states) }
    return inds


def generate(spec, circuit, lib, template):

    context = {
        "lib" : lib,
        "spec" : spec,
        "circuit" : circuit,
        "state_inds": get_state_inds(spec)
    }

    template = Template(read_file(template))

    return template.render(context)


def main():

    output_dir = "generated"

    lib     = load_lib("libraries/workcraft.lib")
    spec    = load_sg("examples/d-element/spec.sg")
    circuit = load_verilog("examples/d-element/circuit.v")

    spec_str    = generate(spec, circuit, lib, "templates/spec.v")
    circuit_str = generate(spec, circuit, lib, "templates/circuit.v")

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    spec_file    = os.path.join(output_dir, "spec.v")
    circuit_file = os.path.join(output_dir, "circuit.v")

    write_file(spec_str, spec_file)
    write_file(circuit_str, circuit_file)


if __name__ == '__main__':
    main()
