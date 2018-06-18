module untitled(n0, n1, n2, n3, n4, n5, n6, n7, n8, n9);

	output n0, n1, n2, n3, n4, n5, n6, n7, n8, n9;

	INV b0 (.I(n0), .ON(n1));
	BUF b1 (.I(n1), .O(n2));
	BUF b2 (.I(n2), .O(n3));
	BUF b3 (.I(n3), .O(n4));
	BUF b4 (.I(n4), .O(n5));
	BUF b5 (.I(n5), .O(n6));
	BUF b6 (.I(n6), .O(n7));
	BUF b7 (.I(n7), .O(n8));
	BUF b8 (.I(n8), .O(n9));
	BUF b9 (.I(n9), .O(n0));

	// signal values at the initial state:
    // !n0 !n1 !n2 !n3 !n4 !n5 !n6 !n7 !n8 !n9

endmodule
