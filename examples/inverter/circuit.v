
module Untitled (ai, bi, co);
    input ai, bi;
    output co;

    // This inverter should have a short delay
    INV _U0 (.ON(ai_n), .I(ai));

    AND2 _U1 (.O(b), .A(ai), .B(ai_n));

    OR2 _21 (.O(co), .A(b), .B(bi));

    // signal values at the initial state:
    // !ai ai_n !bi !co !b
endmodule
