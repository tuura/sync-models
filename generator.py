#!/usr/bin/env python

from jinja2 import Template
from sg_parser import load_sg
from lib_parser import load_lib
from lib_parser import merge_libs
from collections import defaultdict
from verilog_parser import load_verilog

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
    """Return a map: state -> index."""

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


def get_nond_groups(transitions):
    """Return two dicts, inds and counts, representing non-deterministic
    transitions choices.

    'counts' is (before, tr) -> count of (before, tr) in transitions
    'inds' is the index of (before, tr, after) within its group of (before, tr)
    """

    counts = defaultdict(lambda: 0)
    inds = dict()

    for before, tr, after in transitions:
        ckey = (before, tr)
        counts[ckey] += 1
        inds[(before, tr, after)] = counts[ckey]

    return inds, counts


def generate(spec, circuit, lib, template):

    stateful = { inst: body for inst, body in circuit["modules"].iteritems()
        if not body.get("short_delay") }

    stateless = { inst: body for inst, body in circuit["modules"].iteritems()
        if body.get("short_delay") }

    get_output_pin   = lambda mod: lib[mod["type"]]["output"]
    get_output_net   = lambda mod: mod["connections"][get_output_pin(mod)]

    stateful_nets    = sorted(map(get_output_net, stateful.values()))
    stateless_nets   = sorted(map(get_output_net, stateless.values()))
    stateless_outs   = set(circuit["outputs"]) & set(stateless_nets)
    ndinds, ndcounts = get_nond_groups(spec["transitions"])
    ndbits           = bit_size(max(ndcounts.values()))
    inputs           = sorted(spec["inputs"])
    outputs          = sorted(spec["outputs"])
    nets             = inputs + stateful_nets
    firebits         = bit_size(len(nets))
    transitions      = sorted(spec["transitions"])
    firing_indices   = { net: nets.index(net) for net in nets }

    context = {
        "lib"            : lib,
        "inputs"         : inputs,
        "outputs"        : outputs,
        "get_output_net" : get_output_net,
        "get_output_pin" : get_output_pin,
        "firing_indices" : firing_indices,
        "nets"           : nets,
        "transitions"    : transitions,
        "firebits"       : firebits,
        "initial_spec"   : spec["initial_state"],  # string
        "stateless"      : stateless,  # dictionary of stateless modules
        "state_inds"     : get_state_inds(spec),  # state -> index
        "initial_circuit": circuit["initial_state"],  # dict: signal -> state
        "ndinds"         : ndinds,
        "ndcounts"       : ndcounts,
        "ndbits"         : ndbits,
        "stateful"       : stateful,
        "stateful_nets"  : stateful_nets,
        "stateless_outs" : stateless_outs
    }

    template = Template(read_file(template))

    return template.render(context)


def main():

    output_dir = "generated/ifv-perf"

    lib_wk  = load_lib("libraries/workcraft.lib")
    lib_ex  = load_lib("libraries/extra.lib")
    lib     = merge_libs(lib_wk, lib_ex)
    spec    = load_sg("examples/buffers/spec-n30.sg")
    circuit = load_verilog("examples/buffers/buffers-n30.v")

    spec_str    = generate(spec, circuit, lib, "templates/ifv_perf/spec.v")
    circuit_str = generate(spec, circuit, lib, "templates/ifv_perf/circuit.v")

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    spec_file    = os.path.join(output_dir, "spec.v")
    circuit_file = os.path.join(output_dir, "circuit.v")

    write_file(spec_str, spec_file)
    write_file(circuit_str, circuit_file)


if __name__ == '__main__':
    main()
