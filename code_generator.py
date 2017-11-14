#!/usr/bin/env python

from jinja2 import Template
from sg_parser import load_sg
from lib_parser import load_lib
from collections import defaultdict
from verilog_parser import load_verilog
from lib_parser import merge_libs

import os
import re
import json
import math


def read_file(file):
    """Return content of file as a string."""
    with open(file, "r") as fid:
        return fid.read()


def write_file(content, file):
    """Write string 'content' to file."""
    with open(file, "w") as fid:
        fid.write(content)


def get_workcraft_state_ind(state):
    """Attempt to extract state index assuming state name is in the format
    generated by workcraft, e.g. s7_0101101 (returns 7 in this case).

    Return None is the state name cannot be matched.
    """

    reg1 = r"^s([0-9]+)_"
    pat1 = re.compile(reg1, flags=re.MULTILINE)
    matches = pat1.findall(state)
    return int(matches[0]) if len(matches) == 1 else None


def get_state_inds(spec):
    """Returns a map: state -> unique index."""

    froms = [ item[0] for item in spec["transitions"]]
    tos   = [ item[2] for item in spec["transitions"]]

    states = sorted(set(froms + tos))
    workcraft_inds = map(get_workcraft_state_ind, states)
    workcraft_valid = not any([ind is None for ind in workcraft_inds])
    inds = workcraft_inds if workcraft_valid else range(len(states))

    inds = { state: ind for ind, state in zip(inds, states) }
    return inds


def bit_size(n):
    """Return minimum number of bits required to represent n."""
    bits = math.log(n) / math.log(2)
    return int(math.ceil(bits))


def generate(spec, circuit, lib, template):

    context = {
        "lib" : lib,
        "spec" : spec,
        "circuit" : circuit,
        "state_inds": get_state_inds(spec),
        "bit_size": bit_size
    }

    template = Template(read_file(template))

    return template.render(context)


def main():

    output_dir = "generated"

    lib     = load_lib("libraries/workcraft.lib")
    spec    = load_sg("examples/buck-merged/spec.sg")
    circuit = load_verilog("examples/buck-merged/circuit.v")

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
