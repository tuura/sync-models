
from math import ceil
from math import log
from jinja2 import Template
from sg_parser import load_sg
from lib_parser import load_lib
from collections import defaultdict
from verilog_parser import load_verilog

import json

def read_file(file):

    with open(file, "r") as fid:
        return fid.read()


def get_valid_states(spec):
    """Return a map: transition -> [valid pre states]."""

    prior_states = defaultdict(list)

    for before, tr, _ in spec["transitions"]:
        prior_states[tr].append(before)

    return prior_states


def get_states(spec):
    """Return a list of the states in spec."""

    sublists = [ [item[0], item[2]] for item in spec["transitions"] ]
    flattened = sum(sublists, [])
    return sorted(set(flattened))


def get_transitions(spec):
    """Return a list of the states in spec."""

    trs = [ item[1] for item in spec["transitions"] ]
    return sorted(set(trs))


def get_signals(fspec):
    """Return a list of the signals in fspec."""

    signals = [ item[1][1:] for item in fspec["transitions"] ]
    return sorted(set(signals))


def format_tr(tr):
    """Given a transition 'tr' in the form 'req+', 'req-', return the Verilog
    equivalents 'req' and '~req'."""

    signal, sign = tr[:-1], tr[-1]

    prefix = "~" if sign=="-" else " "  # use space to maintain symmetry

    return prefix + signal


def format_spec(spec):

    states = get_states(spec)
    inds = { state: ind for ind, state in enumerate(states) }

    def format_item(item):
        state1, tr, state2 = item
        return [ inds[state1], format_tr(tr), inds[state2] ]

    spec["transitions"] = map(format_item, spec["transitions"])
    spec["initial_state"] = inds[spec["initial_state"]]


def generate_verilog_spec(spec, circuit, template="templates/spec.v"):

    # Prepare data structures for code generation

    states = get_states(spec)

    def get_can_name(tr):
        prefix, signal = tr[0], tr[1:]
        return signal + ("_can_fall" if prefix=="~" else "_can_rise")

    can_transition = { tr: get_can_name(tr) for tr in get_transitions(spec) }

    # Generate

    context = {
        "inputs"         : spec["inputs"],
        "outputs"        : spec["outputs"],
        "signals"        : get_signals(spec),
        "initial"        : spec["initial_state"],
        "state_bits"     : int(ceil(log(len(states)) / log(2))),
        "ena_bits"       : len(circuit["initial_state"]),
        "transitions"    : sorted(spec["transitions"]),
        "valid_states"   : get_valid_states(spec),
        "can_transition" : can_transition,
    }

    template = Template(read_file(template))

    print template.render(context)


def generate_verilog_circuit(spec, circuit, lib, template="templates/circuit.v"):

    context = {
        "lib": lib,
        "spec": spec,
        "circuit": circuit
    }

    template = Template(read_file(template))

    print template.render(context)

def main():

    spec = load_sg("examples/d-element/spec.sg")

    circuit = load_verilog("examples/d-element/circuit.v")

    workcraft_lib = load_lib("libraries/workcraft.lib")

    format_spec(spec)

    # print json.dumps(circuit, indent=4)
    generate_verilog_circuit(spec, circuit, workcraft_lib)
    return

    # generate_properties(spec)
    generate_verilog_spec(spec, circuit)


if __name__ == '__main__':
    main()
