// Verilog netlist generated by Workcraft 3 -- https://workcraft.org/
module concurrency (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b);
    output a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b;

    INV _U0 (.ON(a0), .I(b));
    INV _U1 (.ON(a1), .I(b));
    INV _U2 (.ON(a2), .I(b));
    INV _U3 (.ON(a3), .I(b));
    INV _U4 (.ON(a4), .I(b));
    INV _U5 (.ON(a5), .I(b));
    INV _U6 (.ON(a6), .I(b));
    INV _U7 (.ON(a7), .I(b));
    INV _U8 (.ON(a8), .I(b));
    INV _U9 (.ON(a9), .I(b));
    OAI31 _U10 (.ON(_U10_ON), .A1(a0), .A2(a1), .A3(a5), .B(_U22_ON));
    INV _U11 (.ON(_U11_ON), .I(_U10_ON));
    AO22 _U12 (.O(_U12_O), .A1(_U11_ON), .A2(a0), .B1(b), .B2(_U22_ON));
    AOI32 _U13 (.ON(_U13_ON), .A1(a1), .A2(a9), .A3(_U25_ON), .B1(_U12_O), .B2(_U24_ON));
    NOR2B _U14 (.ON(_U14_ON), .AN(a6), .B(_U13_ON));
    AOI31 _U15 (.ON(_U15_ON), .A1(_U14_ON), .A2(a7), .A3(a8), .B(_U12_O));
    INV _U16 (.ON(_U16_ON), .I(_U15_ON));
    OA22 _U17 (.O(b), .A1(_U12_O), .A2(b), .B1(_U16_ON), .B2(a9));
    OAI31 _U18 (.ON(_U18_ON), .A1(_U14_ON), .A2(a7), .A3(a8), .B(_U16_ON));
    INV _U19 (.ON(_U19_ON), .I(_U18_ON));
    OA21 _U20 (.O(_U20_O), .A1(_U19_ON), .A2(_U11_ON), .B(_U24_ON));
    OAI32 _U21 (.ON(_U21_ON), .A1(a3), .A2(a4), .A3(_U25_ON), .B1(_U12_O), .B2(_U20_O));
    INV _U22 (.ON(_U22_ON), .I(_U21_ON));
    AOI31 _U23 (.ON(_U23_ON), .A1(a3), .A2(a4), .A3(a5), .B(_U20_O));
    INV _U24 (.ON(_U24_ON), .I(_U23_ON));
    NAND2B _U25 (.ON(_U25_ON), .AN(a2), .B(_U13_ON));

    // signal values at the initial state:
    // !a0 !a1 !a2 !a3 !a4 !a5 !a6 !a7 !a8 !a9 _U10_ON !_U11_ON !_U12_O _U13_ON !_U14_ON _U15_ON !_U16_ON !b _U18_ON !_U19_ON !_U20_O _U21_ON !_U22_ON _U23_ON !_U24_ON !_U25_ON
endmodule
