// Verilog netlist generated by Workcraft 3 -- https://workcraft.org/
module Untitled (ao, hl, ro, whl);
    input ao, hl;
    output ro, whl;

    assign whl = _U1_QN;

    AND2 _U0 (.O(ro), .A(hl), .B(_U1_QN));
    NC2 _U1 (.QN(_U1_QN), .A(ao), .B(hl));

    // signal values at the initial state:
    // !whl !ro _U1_QN !ao !hl
endmodule
