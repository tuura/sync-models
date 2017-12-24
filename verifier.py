#!/usr/bin/env python

from docopt import docopt
from sg_parser import load_sg
from lib_parser import load_lib
from lib_parser import merge_libs
from collections import defaultdict
from verilog_parser import load_verilog

import json

usage = """verifier.py

Usage:
  verifier.py [options] <circuit.v> <spec.sg>

Options:
  -q --quiet      Suppress printing state exploration details.
  -l --lib=<dir>  Load libraries from specific directory [default: libraries].

"""


def get_next_state(encoding, state, transition):
    """Compute the next after a transition."""
    signal = transition[:-1]
    ind = encoding.index(signal)  # signal index
    val = 1 if transition[-1] == "+" else 0
    next_state = state[:ind] + (val,) + state[ind+1:]
    return next_state


def get_signal_value(encoding, state, signal):
    """Return signal state/value."""
    ind = encoding.index(signal)
    return state[ind]


def print_underlined(str_):
    print "%s" % str_
    print "%s\n" % ("-" * len(str_))


def unzip(zipped):
    """Unzip zipped lists."""
    return zip(*zipped)


def verify_circuit(lib, circuit, sg, quiet=False):
    """Check if circuit satisfies the spec sg."""

    # Add circuit state connections

    add_state_connections(circuit, lib)

    # Get encoding and initial_state

    encoding, initial_state = unzip(circuit["initial_state"].iteritems())

    # Build a library-independent circuit description (an "implementation")

    implementation = {}

    for module in circuit["modules"].values():

        gate = lib[module["type"]]

        output_pin = gate["output"]

        inputs = { pin: module["connections"][pin] for pin in gate["inputs"]}

        output = module["connections"][gate["output"]]

        implementation[output] = (gate, inputs)

    # Build two data structures from sg:
    #
    # 1. sg_next_states: (prev_state, transition) -> next_state
    #
    # 2. sg_trs: current_state -> set([valid_transition])

    sg_next_states = { (prev_st, tr): next_st
        for prev_st, tr, next_st in sg["transitions"] }

    sg_trs = defaultdict(set)

    for prev_st, tr, _ in sg["transitions"]:
        sg_trs[prev_st].add(tr)

    # Prepare some handy structures and functions

    st_labels = { initial_state: sg["initial_state"] }  # map: state -> label

    inputs  = sg["inputs"]
    outputs = sg["outputs"]
    internals = set(encoding) - set(inputs) - set(outputs)

    pos_tran = lambda signal: "%s+" % signal
    neg_tran = lambda signal: "%s-" % signal

    all_inp_trs = set(map(pos_tran, inputs   ) + map(neg_tran, inputs   ))
    all_out_trs = set(map(pos_tran, outputs  ) + map(neg_tran, outputs  ))
    all_int_trs = set(map(pos_tran, internals) + map(neg_tran, internals))

    visited  = { initial_state }
    to_visit = { initial_state }

    show_state = lambda state: "".join(map(str, state))

    # Enumerate atomic transitions

    # 'atomic_trs' is a map tr1 -> [tr2] where tr2 occurs on the same clock time
    # 'as tr1

    atomic_trs = defaultdict(list)

    short_delay_invs = [ mod for mod in circuit["modules"].values()
        if mod.get("short_delay") ]

    for inv in short_delay_invs:
        inp, out = inv["connections"]["I"], inv["connections"]["ON"]

        atomic_trs[pos_tran(inp)].append(neg_tran(out))
        atomic_trs[neg_tran(inp)].append(pos_tran(out))

    # Explore state space

    nstates = 0

    while to_visit:

        next_to_visit = set()

        for state in to_visit:

            nstates += 1

            label = st_labels[state]

            if not quiet:
                print_underlined("visiting state %s (%s):" % (show_state(state), label))

            visited.add(state)

            # disovering transitions:

            circuit_trs = set()

            for output, (gate, connections) in implementation.iteritems():

                gate_inputs = { port: (get_signal_value(encoding, state, signal))
                    for port, signal in connections.iteritems() }

                next_sig_state = gate["lambda"](**gate_inputs)  # post transition

                if next_sig_state != get_signal_value(encoding, state, output):
                    tran = "%s%s" % (output, "+" if next_sig_state else "-")
                    circuit_trs.add(tran)

            spec_trs = sg_trs[label]

            spec_inp_trs = all_inp_trs & spec_trs
            spec_out_trs = all_out_trs & spec_trs

            # Enumerate output transitions
            circuit_out_trs = circuit_trs & all_out_trs

            # Enumerate output transitions that are not in specs
            invalid_output_trs = circuit_out_trs - spec_trs

            if not quiet:
                print "Transitions (Internal) : %s" % list(circuit_trs & all_int_trs)
                print "Transitions (Input)    : %s" % list(spec_inp_trs)
                print "Transitions (Output)   : %s" % list(circuit_out_trs)
                print ""

            if not (circuit_trs or spec_inp_trs):
                return (False, "Deadlock in state %s (%s)" % (show_state(state), label))

            if invalid_output_trs:

                if not quiet:
                    print "Signal values:\n"
                    for signal, value in zip(encoding, state):
                        print "%10s = %s" % (signal, value)
                    print ""

                return (False, "Found non-compliant circuit output transition(s): %s" %
                    list(invalid_output_trs))

            # discover next states

            for tr in circuit_trs | spec_inp_trs:
                next_state = get_next_state(encoding, state, tr)

                for tr2 in atomic_trs.get(tr, []):
                    next_state = get_next_state(encoding, next_state, tr2)


                next_label = sg_next_states.get((label, tr), label)  # label of next state
                st_labels[next_state] = next_label
                next_to_visit.add(next_state)
                if not quiet:
                    print "Discovered state: %s" % show_state(next_state)

            if not quiet:
                print ""

        to_visit = next_to_visit - visited

        visited.union(to_visit)

    print "Explored %s states" % nstates

    return (True, None)


def add_state_connections(circuit, lib):
    """Add feedback connections to circuit state elements."""

    for module in circuit["modules"].values():

        gate = lib[module["type"]]

        if gate["type"] == "LATCH":
            state_pin = gate["state_input"]
            output_net = module["connections"][gate["output"]]
            module["connections"][state_pin] = output_net


def main():

    # Load library, circuit and spec

    args = docopt(usage, version="verifier.py v0.1")

    spec    = load_sg(args["<spec.sg>"])
    circuit = load_verilog(args["<circuit.v>"])
    lib     = load_lib("%s/*.lib" % args["--lib"])

    result, msg = verify_circuit(lib, circuit, spec, quiet=args["--quiet"])

    print("Result: " + ("PASS" if result else "FAIL"))

    if msg:
        print "Reason: %s" % msg


if __name__ == "__main__":
    main()
