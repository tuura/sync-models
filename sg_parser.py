#!/usr/bin/env python

def load_sg(file):

    sg = { "transitions": [] }

    ignored = [".state", ".end"]

    with open(file, "r") as fid:
        lines = fid.read().splitlines()

    for line in lines:

        if not line or line[0] == '#':
            continue  # ignore blank and comment lines

        words = line.split()

        if words[0] in ignored:
            pass

        elif words[0] == ".model":
            sg["model"] = words[1]

        elif words[0] == ".inputs":
            sg["inputs"] = words[1:]

        elif words[0] == ".outputs":
            sg["outputs"] = words[1:]

        elif words[0] == ".marking":
            sg["initial_state"] = words[1][1:-1]

        else:
            sg["transitions"].append(words)

    return sg


def main():

    sg = load_sg("examples/d-element/spec.sg")
    print(sg)


if __name__ == '__main__':
    main()
