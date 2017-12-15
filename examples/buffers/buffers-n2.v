module untitled(n0, n1, n2);

    output n0, n1, n2;

    BUF u0 (.I(n0), .O(n1));
    BUF u1 (.I(n1), .O(n2));
    BUF u2 (.I(n2), .O(n0));

    // signal values at the initial state:
    // !n0 !n1 !n2

endmodule
