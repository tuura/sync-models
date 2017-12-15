
def main():

    header = """
    module Untitled(ri, ro, ai, ao);

    input ri, ao;
    output ro, ai;
    """

    template = """
    // Stage %(ind)d

    AOI2BB2 U0_%(ind)d (.ON(ai_%(ind)d), .A1N(ao_%(ind)d), .A2N(U2_ON_%(ind)d), .B1(ao_%(ind)d), .B2(ri_%(ind)d));
    AOI2BB2 U1_%(ind)d (.ON(ro_%(ind)d), .A1N(ri_%(ind)d), .A2N(U2_ON_%(ind)d), .B1(ri_%(ind)d), .B2(U2_ON_%(ind)d));
    AOI2BB2 U2_%(ind)d (.ON(U2_ON_%(ind)d), .A1N(ao_%(ind)d), .A2N(U2_ON_%(ind)d), .B1(ao_%(ind)d), .B2(ai_%(ind)d));
    """
    initial_str = "!ai_%(ind)d !ro_%(ind)d !U2_ON_%(ind)d !ao_%(ind)d !ri_%(ind)d"



    template = """
    NOR2 _U0_%(ind)d (.ON(ai_%(ind)d)    , .A(ao_%(ind)d), .B(_U2_QN_%(ind)d));
    AND2 _U1_%(ind)d (.O(ro_%(ind)d)     , .A(ri_%(ind)d), .B(_U2_QN_%(ind)d));
    NC2  _U2_%(ind)d (.QN(_U2_QN_%(ind)d), .A(ao_%(ind)d), .B(ri_%(ind)d));
    """
    initial_str = "!ai_%(ind)d !ro_%(ind)d _U2_QN_%(ind)d !ao_%(ind)d !ri_%(ind)d"

    # // This inverter should have a short delay
    # INV _U0_%(ind)d (.ON(_U0_ON_%(ind)d), .I(ri_%(ind)d));
    # // This inverter should have a short delay
    # INV _U1_%(ind)d (.ON(_U1_ON_%(ind)d), .I(_U5_ON_%(ind)d));
    # OAI22 _U2_%(ind)d (.ON(ro_%(ind)d), .A1(_U1_ON_%(ind)d), .A2(ri_%(ind)d), .B1(_U5_ON_%(ind)d), .B2(_U0_ON_%(ind)d));
    # // This inverter should have a short delay
    # INV _U3_%(ind)d (.ON(_U3_ON_%(ind)d), .I(ao_%(ind)d));
    # // This inverter should have a short delay
    # INV _U4_%(ind)d (.ON(_U4_ON_%(ind)d), .I(_U5_ON_%(ind)d));
    # OAI22 _U5_%(ind)d (.ON(_U5_ON_%(ind)d), .A1(_U4_ON_%(ind)d), .A2(ao_%(ind)d), .B1(ai_%(ind)d), .B2(_U3_ON_%(ind)d));


    backward = """
    BUF ao_%(ind_prev)d_buf (.O(ao_%(ind_prev)d), .I(ai_%(ind_next)d)); // stage %(ind_prev)d <- stage %(ind_next)d
    """

    forward = "    BUF ri_%(ind_next)d_buf (.O(ri_%(ind_next)d), .I(ro_%(ind_prev)d)); // stage %(ind_prev)d -> stage %(ind_next)d"""

    # footer = "    BUF ao_%(id)d_buf (.O(ao_%(id)d), .I(ro_%(id)d));"

    initial = """
    // signal values at the initial state:
    // %s

    endmodule
    """

    n = 2

    def print_fix(content):
        ao_last = "ao_%d" % (n - 1)
        ro_last = "ro_%d" % (n - 1)
        reps = [("ai_0", "ai"), (ro_last, "ro"), (ao_last, "ao"), ("ri_0", "ri")]

        for str1, str2 in reps:
            content = content.replace(str1, str2)
        print content

    print_fix(header.rstrip())

    for ind in range(n):
        print_fix(template.rstrip() % {"ind": ind})

    for ind in range(n-1):
        inds = {"ind_prev": ind, "ind_next": ind+1}
        print_fix(backward.rstrip() % inds)
        print_fix(forward.rstrip()  % inds)


    parts = [initial_str % {"ind": ind} for ind in range(n) ]

    # print_fix(footer.rstrip() % {"id": n-1})

    print_fix(initial % " ".join(parts))




if __name__ == '__main__':
    main()