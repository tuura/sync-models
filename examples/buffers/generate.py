import sys

def main():
    n = int(sys.argv[1])

    ns = ["n%d" % x for x in range(n)]

    ns_str = ", ".join(ns)

    def pind(line):
        print "    %s" % line

    print "module Untitled (%s);" % ns_str
    pind("");
    pind("output %s;" % ns_str)
    pind("");

    for ind in range(n):
        inst = "BUF" if ind else "INV"
        src = "n%d" % ind
        dst = "n%d" % (ind+1 if (ind<n-1) else 0)
        pin = "O" if ind else "ON"
        pind("%s b%d (.I(%s), .%s(%s));" % (inst, ind, src, pin, dst))

    neg_ns = ["!n%d" % x for x in range(n)]

    pind("");
    pind("// signal values at the initial state:")
    pind("// %s" % " ".join(neg_ns))
    pind("");

    print "endmodule"


if __name__ == '__main__':
    main()