// Verilog netlist generated by Workcraft 3 -- https://workcraft.org/
module concurrency (a0, a1, a2, a3, a4, a5, a6, a7, a8, b);
    output a0, a1, a2, a3, a4, a5, a6, a7, a8, b;

    INV _U0 (.ON(a0), .I(b));
    INV _U1 (.ON(a1), .I(b));
    INV _U2 (.ON(a2), .I(b));
    INV _U3 (.ON(a3), .I(b));
    INV _U4 (.ON(a4), .I(b));
    INV _U5 (.ON(a5), .I(b));
    INV _U6 (.ON(a6), .I(b));
    INV _U7 (.ON(a7), .I(b));
    INV _U8 (.ON(a8), .I(b));
    // This inverter should have a short delay
    INV _U9 (.ON(_U9_ON), .I(b));
    // This inverter should have a short delay
    INV _U10 (.ON(_U10_ON), .I(_U23_O));
    AOI31 _U11 (.ON(_U11_ON), .A1(a0), .A2(a1), .A3(a5), .B(_U10_ON));
    NOR4B _U12 (.ON(_U12_ON), .AN(_U11_ON), .B(a2), .C(a3), .D(a7));
    AO21 _U13 (.O(_U13_O), .A1(_U23_O), .A2(_U9_ON), .B(_U12_ON));
    INV _U14 (.ON(_U14_ON), .I(_U13_O));
    // This inverter should have a short delay
    INV _U15 (.ON(_U15_ON), .I(_U24_ON));
    AOI32 _U16 (.ON(_U16_ON), .A1(_U15_ON), .A2(a2), .A3(a3), .B1(_U14_ON), .B2(b));
    INV _U17 (.ON(_U17_ON), .I(_U16_ON));
    C2 _U18 (.Q(b), .A(_U17_ON), .B(a8));
    OAI31 _U19 (.ON(_U19_ON), .A1(a1), .A2(a5), .A3(a6), .B(_U14_ON));
    NAND2 _U20 (.ON(_U20_ON), .A(_U24_ON), .B(_U19_ON));
    // This inverter should have a short delay
    INV _U21 (.ON(_U21_ON), .I(_U20_ON));
    AOI32 _U22 (.ON(_U22_ON), .A1(a6), .A2(a7), .A3(a8), .B1(_U17_ON), .B2(a0));
    AO21 _U23 (.O(_U23_O), .A1(_U21_ON), .A2(_U22_ON), .B(_U11_ON));
    NAND2 _U24 (.ON(_U24_ON), .A(_U20_ON), .B(a4));

    // signal values at the initial state:
    // !a0 !a1 !a2 !a3 !a4 !a5 !a6 !a7 !a8 _U9_ON !_U10_ON _U11_ON _U12_ON _U13_O !_U14_ON !_U15_ON _U16_ON !_U17_ON !b _U19_ON !_U20_ON _U21_ON _U22_ON _U23_O _U24_ON
endmodule
