// Verilog netlist generated by Workcraft 3 -- https://workcraft.org/
module Untitled (gn, gp, oc, uv, zc, gn_ack, gp_ack);
    input oc, uv, zc, gn_ack, gp_ack;
    output gn, gp;

    NOR2B U1 (.ON(U1_ON), .AN(oc), .B(gp_ack));
    NOR2 U3 (.ON(U3_ON), .A(zc), .B(uv));
    C2 U4 (.Q(gn), .A(U1_ON), .B(U3_ON));
    NOR2 U6 (.ON(U6_ON), .A(gn_ack), .B(oc));
    C2 U7 (.Q(gp), .A(uv), .B(U6_ON));

    // signal values at the initial state:
    // !U1_ON U3_ON gn !U6_ON !gp !oc !uv !zc gn_ack !gp_ack
endmodule