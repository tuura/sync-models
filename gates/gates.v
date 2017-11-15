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


module INV (output ON, input I);
    assign ON = ~I;
endmodule


module BUF (output O, input I);
    assign O = I;
endmodule


module AND2 (output O, input A, input B);
    assign O = A & B;
endmodule


module OR2 (output O, input A, input B);
    assign O = A | B;
endmodule


module NOR2 (output ON, input A, input B);
    assign ON = ~(A | B);
endmodule

module NOR3 (output ON, input A, input B, input C);
    assign ON = ~(A | B |C);
endmodule

module NOR2B (output ON, input AN, input B);
    assign A = ~AN;
    assign ON = ~(A | B);
endmodule


module OA211 (output O, input A1, input A2, input B, input C);
    assign O = (A1 | A2) & B & C;
endmodule

module OR3B (output O, input AN, input B, input C);
    assign O = (~AN | B | C);
endmodule

module AO22 (output O, input A1, input A2, input B1, input B2);
    assign O = (A1 & A2) | (B1 & B2);
endmodule

module AND2B (output O, input AN, input B);
    assign O = ~AN & B;
endmodule

module GATE1 (output ON, input A1N, input A2N, input B);
    assign ON = ~((~A1N & ~A2N) | B);
endmodule

module OA21 (output O, input A1, input A2, input B);
    assign O = (A1 | A2) & B;
endmodule

module AO21 (output O, input A1, input A2, input B);
    assign O = (A1 & A2) | B;
endmodule

module NOR4BB (output ON, input AN, input BN, input C, input D);
    assign ON = ~(~AN | ~BN | C | D);
endmodule
