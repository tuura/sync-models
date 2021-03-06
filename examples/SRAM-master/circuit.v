// Verilog netlist generated by Workcraft 3 -- https://workcraft.org/
module UNTITLED (readReady, rr, wr, writeDone, ra, read, wa, write);
    input readReady, rr, wr, writeDone;
    output ra, read, wa, write;

    NOR4BB _U0 (.ON(ra), .AN(readReady), .BN(read), .C(wr), .D(writeDone));
    NOR2 _U1 (.ON(_U1_ON), .A(readReady), .B(writeDone));
    // This inverter should have a short delay
    INV _U2 (.ON(_U2_ON), .I(wa));
    AO21 _U3 (.O(_U3_O), .A1(_U2_ON), .A2(wr), .B(rr));
    C2 _U4 (.Q(read), .A(_U1_ON), .B(_U3_O));
    AO22 _U5 (.O(wa), .A1(wr), .A2(wa), .B1(write), .B2(writeDone));
    NOR4BB _U6 (.ON(write), .AN(readReady), .BN(read), .C(rr), .D(ra));

    // signal values at the initial state:
    // !ra _U1_ON _U2_ON !_U3_O !read !wa !write !readReady !rr !wr !writeDone
endmodule
