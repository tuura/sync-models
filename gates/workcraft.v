module NOR3 (output ON, input A, input C, input B);
    assign ON = ~(A | B | C);
endmodule

module NOR2 (output ON, input A, input B);
    assign ON = ~(A | B);
endmodule

module NOR4 (output ON, input A, input C, input B, input D);
    assign ON = ~(A | B | C | D);
endmodule

module NAND4BB (output ON, input BN, input AN, input C, input D);
    assign ON = ~(~AN & ~BN & C & D);
endmodule

module OR4 (output O, input A, input C, input B, input D);
    assign O = A | B | C | D;
endmodule

module OAI21 (output ON, input A1, input B, input A2);
    assign ON = ~((A1 | A2) & B);
endmodule

module NAND2 (output ON, input A, input B);
    assign ON = ~(A & B);
endmodule

module NAND3 (output ON, input A, input C, input B);
    assign ON = ~(A & B & C);
endmodule

module NOR4B (output ON, input C, input B, input D, input AN);
    assign ON = ~(~AN | B | C | D);
endmodule

module LOGIC1 (output O);
    assign O = 1;
endmodule

module OAI211 (output ON, input A1, input C, input B, input A2);
    assign ON = ~((A1 | A2) & B & C);
endmodule

module NAND2B (output ON, input B, input AN);
    assign ON = ~(~AN & B);
endmodule

module NOR4BB (output ON, input BN, input AN, input C, input D);
    assign ON = ~(~AN | ~BN | C | D);
endmodule

module AOI22 (output ON, input A1, input A2, input B1, input B2);
    assign ON = ~(A1 & A2 | B1 & B2);
endmodule

module NAND4B (output ON, input C, input B, input D, input AN);
    assign ON = ~(~AN & B & C & D);
endmodule

module OAI2BB2 (output ON, input A2N, input A1N, input B1, input B2);
    assign ON = ~((~A1N | ~A2N) & (B1 | B2));
endmodule

module AOI21 (output ON, input A1, input B, input A2);
    assign ON = ~(A1 & A2 | B);
endmodule

module NOR2B (output ON, input B, input AN);
    assign ON = ~(~AN | B);
endmodule

module AO22 (output O, input A1, input A2, input B1, input B2);
    assign O = A1 & A2 | B1 & B2;
endmodule

module AOI2BB1 (output ON, input B, input A2N, input A1N);
    assign ON = ~(~A1N & ~A2N | B);
endmodule

module BUF (output O, input I);
    assign O = I;
endmodule

module NAND4 (output ON, input A, input C, input B, input D);
    assign ON = ~(A & B & C & D);
endmodule

module OAI32 (output ON, input A1, input A3, input A2, input B1, input B2);
    assign ON = ~((A1 | A2 | A3) & (B1 | B2));
endmodule

module OAI22 (output ON, input A1, input A2, input B1, input B2);
    assign ON = ~((A1 | A2) & (B1 | B2));
endmodule

module OAI33 (output ON, input A1, input A3, input A2, input B1, input B2, input B3);
    assign ON = ~((A1 | A2 | A3) & (B1 | B2 | B3));
endmodule

module OAI31 (output ON, input A1, input A3, input A2, input B);
    assign ON = ~((A1 | A2 | A3) & B);
endmodule

module OR2 (output O, input A, input B);
    assign O = A | B;
endmodule

module AOI2BB2 (output ON, input A2N, input A1N, input B1, input B2);
    assign ON = ~(~A1N & ~A2N | B1 & B2);
endmodule

module NOR3B (output ON, input C, input B, input AN);
    assign ON = ~(~AN | B | C);
endmodule

module OR3 (output O, input A, input C, input B);
    assign O = A | B | C;
endmodule

module OAI221 (output ON, input A1, input C, input A2, input B1, input B2);
    assign ON = ~((A1 | A2) & (B1 | B2) & C);
endmodule

module OAI222 (output ON, input A1, input A2, input B1, input B2, input C2, input C1);
    assign ON = ~((A1 | A2) & (B1 | B2) & (C1 | C2));
endmodule

module OA22 (output O, input A1, input A2, input B1, input B2);
    assign O = (A1 | A2) & (B1 | B2);
endmodule

module OA21 (output O, input A1, input B, input A2);
    assign O = (A1 | A2) & B;
endmodule

module AND4 (output O, input A, input C, input B, input D);
    assign O = A & B & C & D;
endmodule

module AO21 (output O, input A1, input B, input A2);
    assign O = A1 & A2 | B;
endmodule

module NAND3B (output ON, input C, input B, input AN);
    assign ON = ~(~AN & B & C);
endmodule

module AND3 (output O, input A, input C, input B);
    assign O = A & B & C;
endmodule

module AND2 (output O, input A, input B);
    assign O = A & B;
endmodule

module AOI31 (output ON, input A1, input A3, input A2, input B);
    assign ON = ~(A1 & A2 & A3 | B);
endmodule

module INV (output ON, input I);
    assign ON = ~I;
endmodule

module AOI32 (output ON, input A1, input A3, input A2, input B1, input B2);
    assign ON = ~(A1 & A2 & A3 | B1 & B2);
endmodule

module AOI211 (output ON, input A1, input C, input B, input A2);
    assign ON = ~(A1 & A2 | B | C);
endmodule

module AOI221 (output ON, input A1, input C, input A2, input B1, input B2);
    assign ON = ~(A1 & A2 | B1 & B2 | C);
endmodule

module AOI222 (output ON, input A1, input A2, input B1, input B2, input C2, input C1);
    assign ON = ~(A1 & A2 | B1 & B2 | C1 & C2);
endmodule

module OAI2BB1 (output ON, input B, input A2N, input A1N);
    assign ON = ~((~A1N | ~A2N) & B);
endmodule

module AOI33 (output ON, input A1, input A3, input A2, input B1, input B2, input B3);
    assign ON = ~(A1 & A2 & A3 | B1 & B2 & B3);
endmodule

module LOGIC0 (output O);
    assign O = 0;
endmodule