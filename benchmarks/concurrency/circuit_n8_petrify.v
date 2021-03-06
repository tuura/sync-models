// Verilog netlist generated by Workcraft 3 -- https://workcraft.org/
module concurrency (a0, a1, a2, a3, a4, a5, a6, a7, b);
    output a0, a1, a2, a3, a4, a5, a6, a7, b;

    INV _U0 (.ON(a0), .I(b));
    INV _U1 (.ON(a1), .I(b));
    INV _U2 (.ON(a2), .I(b));
    INV _U3 (.ON(a3), .I(b));
    INV _U4 (.ON(a4), .I(b));
    INV _U5 (.ON(a5), .I(b));
    INV _U6 (.ON(a6), .I(b));
    INV _U7 (.ON(a7), .I(b));
    // This inverter should have a short delay
    INV _U8 (.ON(_U8_ON), .I(a0));
    NAND4B _U9 (.ON(_U9_ON), .AN(_U19_ON), .B(a2), .C(a3), .D(a6));
    OAI2BB1 _U10 (.ON(_U10_ON), .A1N(b), .A2N(_U18_ON), .B(_U9_ON));
    AND4 _U11 (.O(_U11_O), .A(a0), .B(a1), .C(a5), .D(a7));
    AOI221 _U12 (.ON(_U12_ON), .A1(_U8_ON), .A2(_U11_O), .B1(b), .B2(a7), .C(_U10_ON));
    INV _U13 (.ON(b), .I(_U12_ON));
    // This inverter should have a short delay
    INV _U14 (.ON(_U14_ON), .I(_U19_ON));
    OAI22 _U15 (.ON(_U15_ON), .A1(_U10_ON), .A2(_U11_O), .B1(_U14_ON), .B2(a4));
    OAI31 _U16 (.ON(_U16_ON), .A1(a0), .A2(a1), .A3(a5), .B(_U18_ON));
    INV _U17 (.ON(_U17_ON), .I(_U16_ON));
    NAND2B _U18 (.ON(_U18_ON), .AN(_U17_ON), .B(_U15_ON));
    OAI32 _U19 (.ON(_U19_ON), .A1(a2), .A2(a3), .A3(a6), .B1(_U10_ON), .B2(_U17_ON));

    // signal values at the initial state:
    // !a0 !a1 !a2 !a3 !a4 !a5 !a6 !a7 _U8_ON _U9_ON !_U10_ON !_U11_O _U12_ON !b !_U14_ON _U15_ON _U16_ON !_U17_ON !_U18_ON _U19_ON
endmodule
