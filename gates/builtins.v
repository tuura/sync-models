module BUF_BUILTIN (output out, input inp);
    assign out = inp;
endmodule

module AND2B (output O, input AN, input B);
    assign O = (~AN & B);
endmodule
