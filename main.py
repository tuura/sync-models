#!/usr/bin/env python

from gates import and_gate
from gates import celem_var1
from gates import nor_gate
from sg_parser import load_sg
from collections import defaultdict

import json


def get_next_state(encoding, state, transition):
    signal = transition[:-1]
    ind = encoding.index(signal)  # signal index
    val = 1 if transition[-1] == "+" else 0
    next_state = state[:ind] + (val,) + state[ind+1:]
    return next_state


def get_signal_value(encoding, state, signal):
    ind = encoding.index(signal)
    return state[ind]


def print_underlined(str_):
    print "%s" % str_
    print "%s\n" % ("-" * len(str_))


def in_list(list_):
    """Return a function that checks if item is in list"""
    return lambda item: item in list_


def not_in_list(list_):
    """Return a function that checks if item is not in list"""
    return lambda item: item in list_


def verify_circuit(circuit, sg):
    """Check if circuit satisfies the spec sg"""

    encoding = circuit["encoding"]
    initial_state = circuit["initial_state"]
    implementation = circuit["implementation"]


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

    # Explore state space

    while to_visit:

        next_to_visit = set()

        for state in to_visit:

            label = st_labels[state]

            print_underlined("visiting state %s (%s):" % (str(state), label))

            visited.add(state)

            # disovering transitions:

            implementation_trs = set()

            for output, (gate, inputs) in implementation.iteritems():

                input_values = [get_signal_value(encoding, state, input_)
                    for input_ in inputs ]

                next_sig_state = gate(*input_values)  # post transition

                if next_sig_state != get_signal_value(encoding, state, output):
                    tran = "%s%s" % (output, "+" if next_sig_state else "-")
                    implementation_trs.add(tran)

            spec_trs = sg_trs[label]

            spec_inp_trs = all_inp_trs & spec_trs
            spec_out_trs = all_out_trs & spec_trs

            # Enumerate output transitions
            implementation_out_trs = implementation_trs & all_out_trs

            # Enumerate output transitions that are not in specs
            invalid_output_trs = implementation_out_trs - spec_trs

            print "Transitions (Internal) : %s" % list(implementation_trs & all_int_trs)
            print "Transitions (Input)    : %s" % list(spec_inp_trs)
            print "Transitions (Output)   : %s" % list(implementation_out_trs)
            print ""

            if invalid_output_trs:
                raise Exception("Found non-compliant implementation output transitions: %s", invalid_output_trs)

            # discover next states

            for tr in implementation_trs | spec_inp_trs:
                next_state = get_next_state(encoding, state, tr)
                next_label = sg_next_states.get((label, tr), label)  # label of next state
                st_labels[next_state] = next_label
                next_to_visit.add(next_state)
                print "discovered: %s" % str(next_state)

            print ""

        to_visit = next_to_visit - visited

        visited.union(to_visit)

    return True


def main():

    circuit = {
        "implementation": {
            "ro": (and_gate,   ("ri", "n1")),
            "n1": (celem_var1, ("n1", "ao", "ri")),
            "ai": (nor_gate,   ("n1", "ao"))
        },
        "encoding": ["ri", "ro", "ai", "ao", "n1"],
        "initial_state": (0,0,0,0,1)
    }

    sg = load_sg("examples/d-element/spec.sg")

    result = verify_circuit(circuit, sg)

    print("Result: %s" % ("PASS" if result else "FAIL"))


if __name__ == "__main__":
    main()
