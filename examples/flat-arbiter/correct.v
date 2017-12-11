// Verilog netlist generated by Workcraft 3 -- https://workcraft.org/
module UNTITLED (r1, r2, r3, g1, g2, g3);
    input r1, r2, r3;
    output g1, g2, g3;

    AND2B fab (.O(fab_O), .B(M1a_Q), .AN(g2));
    AND2B fac (.O(fac_O), .B(M2a_Q), .AN(g3));
    AND2B fba (.O(fba_O), .B(M1b_Q), .AN(g1));
    AND2B fbc (.O(fbc_O), .B(M3a_Q), .AN(g3));
    AND2B M1a (.O(M1a_Q), .AN(M1b_Q), .B(r1));
    AND2B M1b (.O(M1b_Q), .AN(M1a_Q), .B(r2));
    AND2B M2a (.O(M2a_Q), .AN(M2b_Q), .B(r1));
    AND2B M2b (.O(M2b_Q), .AN(M2a_Q), .B(r3));
    AND2B M3a (.O(M3a_Q), .AN(M3b_Q), .B(r2));
    AND2B M3b (.O(M3b_Q), .AN(M3a_Q), .B(r3));

    AND3 dac (.O(dac_O), .A(wA_O), .B(fca_Q), .C(fbc_O));
    AND3 dbc (.O(dbc_O), .A(fac_O), .B(wB_O), .C(fcb_Q));

    C2 o3 (.Q(g3), .A(fca_Q), .B(fcb_Q));
    C3 o1 (.Q(g1), .A(fab_O), .B(wA_O), .C(gac_O));
    C3 o2 (.Q(g2), .A(fba_O), .B(wB_O), .C(gbc_O));

    OR2 gac (.O(gac_O), .A(dac_O), .B(fac_O));
    OR2 gbc (.O(gbc_O), .A(dbc_O), .B(fbc_O));
    OR2 wA (.O(wA_O), .A(fab_O), .B(fac_O));
    OR2 wB (.O(wB_O), .A(fba_O), .B(fbc_O));

    SR fca (.Q(fca_Q), .S(M2b_Q), .R(g1));
    SR fcb (.Q(fcb_Q), .S(M3b_Q), .R(g2));

    // signal values at the initial state:
    // !g1 !fab_O !fba_O !fac_O !fbc_O !fca_Q !wA_O !dac_O !gac_O !g2 !g3 !dbc_O !wB_O !gbc_O !fcb_Q !M2a_Q !M3a_Q !M3b_Q !M2b_Q !M1a_Q !M1b_Q !r1 !r2 !r3
endmodule
