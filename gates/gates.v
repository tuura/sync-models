module DFF (CK, RS, ST, D, Q, ENA);

    input CK, RS, ST, D, ENA;
    output reg Q;

    always @(posedge CK or posedge RS or posedge ST) begin
             if (RS)  Q <= 0;
        else if (ST)  Q <= 1;
        else if (CK && ENA) Q <= D;
    end

endmodule


module NC2 (CK, RS, ST, A, B, QN, ENA, PRECAP);

    input CK, RS, ST, A, B, ENA;
    output QN, PRECAP;

    C2 u1 (CK, RS, ST, ~A, ~B, QN, ENA);

endmodule


module C2 (CK, RS, ST, A, B, Q, ENA, PRECAP);

    input CK, RS, ST, A, B, ENA;
    output reg Q;
    output reg PRECAP; // pre-capture or "next" value

    always @(A, B, Q) begin
             if ( A &&  B) PRECAP <= 1;
        else if (~A && ~B) PRECAP <= 0;
        else               PRECAP <= Q;
    end

    always @(posedge CK or posedge RS or posedge ST) begin
             if (RS)        Q <= 0;
        else if (ST)        Q <= 1;
        else if (CK && ENA) Q <= PRECAP;
    end

endmodule
