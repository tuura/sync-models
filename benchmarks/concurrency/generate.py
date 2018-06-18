#!/usr/bin/env python

"""Usage:
python generate.py <n>
"""

import sys
import subprocess


def main():
    n = int(sys.argv[1]) if len(sys.argv)>1 else 10
    g_content = generate_g(n)
    print g_content
    return
    write_file("/tmp/temp.g", g_content)
    subprocess.call("petrify -huge -write_sg temp.g > out.sg", shell=True, cwd="/tmp")
    sg_content = read_file("/tmp/out.sg")
    write_file("spec.sg", sg_content)
    subprocess.call("petrify -tm -lib C:\\\\bin\\\\workcraft\\\\libraries\\\\workcraft.lib -o result.g -vl petrify.v spec.g", shell=True)



def read_file(file):
    with open(file, "r") as fid:
        return fid.read()


def write_file(file, content):
    with open(file, "w") as fid:
        fid.write(content)


def generate_g(n=10):

    header = """.model concurrency
    .outputs %s
    .graph
    """

    transitions = """
    a%i+ b+
    b+ a%i-
    a%i- b-
    b- a%i+"""

    footer = """
    .marking {%s}
    .end
    """

    ais     = ["a%d" % x for x in range(n)]
    initial = ["<b-, a%d+>" % x for x in range(n)]

    fheader = header % " ".join(ais + ["b"])
    body    = "\n".join([ transitions.replace("%i", str(i)) for i in range(n) ])
    ffooter = footer % " ".join(initial)

    content = fheader + body + ffooter

    lines = [ line.strip() for line in content.split("\n") ]
    flines = ["%s\n" % line for line in lines if line]
    content = "".join(flines)

    return content


if __name__ == '__main__':
    main()