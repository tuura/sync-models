module DFF (CK, RS, ST, D, Q, ENA);

    input CK, RS, ST, D, ENA;
    output reg Q;

    always @(posedge CK) begin
             if (RS)  Q <= 0;
        else if (ST)  Q <= 1;
        else if (CK && ENA) Q <= D;
    end

endmodule


module NC2 (CK, RS, ST, A, B, QN, ENA, PRECAP);

    input CK, RS, ST, A, B, ENA;
    output QN, PRECAP;

    C2 u1 (CK, RS, ST, ~A, ~B, QN, ENA, PRECAP);

endmodule


module C2 (CK, RS, ST, A, B, Q, ENA, PRECAP);

    input CK, RS, ST, A, B, ENA;
    output reg Q;
    output reg PRECAP; // pre-capture or "next" value

    always @(A, B, Q) begin
             if ( A &&  B) PRECAP = 1;
        else if (!A && !B) PRECAP = 0;
        else               PRECAP = Q;
    end

    always @(posedge CK) begin
             if (RS)                    Q <= 0;
        else if (ST)                    Q <= 1;
        else if (CK && ENA &&  A &&  B) Q <= 1;
        else if (CK && ENA && !A && !B) Q <= 0;
    end

endmodule


module C3 (CK, RS, ST, A, B, C, Q, ENA, PRECAP);

    input CK, RS, ST, A, B, C, ENA;
    output reg Q;
    output reg PRECAP; // pre-capture or "next" value

    always @(A, B, C) begin
             if ( A &&  B &&  C) PRECAP = 1;
        else if (!A && !B && !C) PRECAP = 0;
        else                     PRECAP = Q;
    end

    always @(posedge CK or posedge RS or posedge ST) begin
             if (RS)                          Q <= 0;
        else if (ST)                          Q <= 1;
        else if (CK && ENA &&  A &&  B &&  C) Q <= 1;
        else if (CK && ENA && ~A && ~B && ~C) Q <= 0;
    end

endmodule

module SR (CK, RS, ST, S, R, Q, ENA, PRECAP);

    input CK, RS, ST, S, R, ENA;
    output reg Q;
    output reg PRECAP; // pre-capture or "next" value

    always @(S, R) begin
             if (S & ~R) PRECAP = 1;
        else if (~S)     PRECAP = 0;
        else             PRECAP = Q;
    end

    always @(posedge CK or posedge RS or posedge ST) begin
             if (RS)                  Q <= 0;
        else if (ST)                  Q <= 1;
        else if (CK && ENA && S & ~R) Q <= 1;
        else if (CK && ENA &&     ~S) Q <= 0;
    end

endmodule