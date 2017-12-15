module untitled (n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19);

	output n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19;

	INV b0  (.I(n0 ), .ON(n1));
	BUF b1  (.I(n1 ), .O(n2));
	BUF b2  (.I(n2 ), .O(n3));
	BUF b3  (.I(n3 ), .O(n4));
	BUF b4  (.I(n4 ), .O(n5));
	BUF b5  (.I(n5 ), .O(n6));
	BUF b6  (.I(n6 ), .O(n7));
	BUF b7  (.I(n7 ), .O(n8));
	BUF b8  (.I(n8 ), .O(n9));
	BUF b9  (.I(n9 ), .O(n10));
	BUF b10 (.I(n10), .O(n11));
	BUF b11 (.I(n11), .O(n12));
	BUF b12 (.I(n12), .O(n13));
	BUF b13 (.I(n13), .O(n14));
	BUF b14 (.I(n14), .O(n15));
	BUF b15 (.I(n15), .O(n16));
	BUF b16 (.I(n16), .O(n17));
	BUF b17 (.I(n17), .O(n18));
	BUF b18 (.I(n18), .O(n19));
	BUF b19 (.I(n19), .O(n0));

	// signal values at the initial state:
    // !n0 !n1 !n2 !n3 !n4 !n5 !n6 !n7 !n8 !n9

endmodule
