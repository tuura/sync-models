import sys
import itertools


def get_handshake_sg(n1, n2, transitions):
    """Return a SG consisting of a cycled sequence of 'transitions', starting
    from state 'n1' and ending with state 'n2'."""

    states = range(n1, n2+1)

    return [ (ind, tr, ind+1) for ind, tr in zip(states, itertools.cycle(transitions)) ]


def print_sg(sg):

    show_state = lambda state: "s%d" % state

    header = [
        "# SG file",
        ".model Untitled",
        ".outputs ai ro",
        ".inputs ri ao",
        ".state graph"
    ]

    body = ["s%d %s s%d" % item for item in sg]

    footer = [
        r".marking {s0}",
        ".end"
    ]

    lines = header + body + footer

    for line in lines:
        print line


def main():

    nstages = int(sys.argv[1])

    output_trs = ["ro+", "ao+", "ro-", "ao-"]

    n = 2 ** nstages  # number of output transitions per input handshake

    trs = ["ri+"] + output_trs*(n/2) + ["ai+", "ri-"] + output_trs*(n/2) + ["ai-"]

    total = len(trs)  # number of states

    next_state = lambda state: (state+1) % total

    states = range(len(trs))

    sg = [ (ind, tr, next_state(ind)) for ind, tr in zip(states, trs)]

    print_sg(sg)



if __name__ == '__main__':
    main()
