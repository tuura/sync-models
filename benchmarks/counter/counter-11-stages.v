
    module Untitled();

    // assign ri_0 = !ai_0;

    BUF buf1 (.O (ai_0_buf), .I(ai_0));
    INV inv1 (.ON(ri_0), .I(ai_0_buf));

    // loop back

    BUF ao_9_buff (.O(ao_9), .I(ro_9) );

    // Stage 0

    AOI2BB2 U0_0 (.ON(ai_0), .A1N(ao_0), .A2N(U2_ON_0), .B1(ao_0), .B2(ri_0));
    AOI2BB2 U1_0 (.ON(ro_0), .A1N(ri_0), .A2N(U2_ON_0), .B1(ri_0), .B2(U2_ON_0));
    AOI2BB2 U2_0 (.ON(U2_ON_0), .A1N(ao_0), .A2N(U2_ON_0), .B1(ao_0), .B2(ai_0));

    // Stage 1

    AOI2BB2 U0_1 (.ON(ai_1), .A1N(ao_1), .A2N(U2_ON_1), .B1(ao_1), .B2(ri_1));
    AOI2BB2 U1_1 (.ON(ro_1), .A1N(ri_1), .A2N(U2_ON_1), .B1(ri_1), .B2(U2_ON_1));
    AOI2BB2 U2_1 (.ON(U2_ON_1), .A1N(ao_1), .A2N(U2_ON_1), .B1(ao_1), .B2(ai_1));

    // Stage 2

    AOI2BB2 U0_2 (.ON(ai_2), .A1N(ao_2), .A2N(U2_ON_2), .B1(ao_2), .B2(ri_2));
    AOI2BB2 U1_2 (.ON(ro_2), .A1N(ri_2), .A2N(U2_ON_2), .B1(ri_2), .B2(U2_ON_2));
    AOI2BB2 U2_2 (.ON(U2_ON_2), .A1N(ao_2), .A2N(U2_ON_2), .B1(ao_2), .B2(ai_2));

    // Stage 3

    AOI2BB2 U0_3 (.ON(ai_3), .A1N(ao_3), .A2N(U2_ON_3), .B1(ao_3), .B2(ri_3));
    AOI2BB2 U1_3 (.ON(ro_3), .A1N(ri_3), .A2N(U2_ON_3), .B1(ri_3), .B2(U2_ON_3));
    AOI2BB2 U2_3 (.ON(U2_ON_3), .A1N(ao_3), .A2N(U2_ON_3), .B1(ao_3), .B2(ai_3));

    // Stage 4

    AOI2BB2 U0_4 (.ON(ai_4), .A1N(ao_4), .A2N(U2_ON_4), .B1(ao_4), .B2(ri_4));
    AOI2BB2 U1_4 (.ON(ro_4), .A1N(ri_4), .A2N(U2_ON_4), .B1(ri_4), .B2(U2_ON_4));
    AOI2BB2 U2_4 (.ON(U2_ON_4), .A1N(ao_4), .A2N(U2_ON_4), .B1(ao_4), .B2(ai_4));

    // Stage 5

    AOI2BB2 U0_5 (.ON(ai_5), .A1N(ao_5), .A2N(U2_ON_5), .B1(ao_5), .B2(ri_5));
    AOI2BB2 U1_5 (.ON(ro_5), .A1N(ri_5), .A2N(U2_ON_5), .B1(ri_5), .B2(U2_ON_5));
    AOI2BB2 U2_5 (.ON(U2_ON_5), .A1N(ao_5), .A2N(U2_ON_5), .B1(ao_5), .B2(ai_5));

    // Stage 6

    AOI2BB2 U0_6 (.ON(ai_6), .A1N(ao_6), .A2N(U2_ON_6), .B1(ao_6), .B2(ri_6));
    AOI2BB2 U1_6 (.ON(ro_6), .A1N(ri_6), .A2N(U2_ON_6), .B1(ri_6), .B2(U2_ON_6));
    AOI2BB2 U2_6 (.ON(U2_ON_6), .A1N(ao_6), .A2N(U2_ON_6), .B1(ao_6), .B2(ai_6));

    // Stage 7

    AOI2BB2 U0_7 (.ON(ai_7), .A1N(ao_7), .A2N(U2_ON_7), .B1(ao_7), .B2(ri_7));
    AOI2BB2 U1_7 (.ON(ro_7), .A1N(ri_7), .A2N(U2_ON_7), .B1(ri_7), .B2(U2_ON_7));
    AOI2BB2 U2_7 (.ON(U2_ON_7), .A1N(ao_7), .A2N(U2_ON_7), .B1(ao_7), .B2(ai_7));

    // Stage 8

    AOI2BB2 U0_8 (.ON(ai_8), .A1N(ao_8), .A2N(U2_ON_8), .B1(ao_8), .B2(ri_8));
    AOI2BB2 U1_8 (.ON(ro_8), .A1N(ri_8), .A2N(U2_ON_8), .B1(ri_8), .B2(U2_ON_8));
    AOI2BB2 U2_8 (.ON(U2_ON_8), .A1N(ao_8), .A2N(U2_ON_8), .B1(ao_8), .B2(ai_8));

    // Stage 9

    AOI2BB2 U0_9 (.ON(ai_9), .A1N(ao_9), .A2N(U2_ON_9), .B1(ao_9), .B2(ri_9));
    AOI2BB2 U1_9 (.ON(ro_9), .A1N(ri_9), .A2N(U2_ON_9), .B1(ri_9), .B2(U2_ON_9));
    AOI2BB2 U2_9 (.ON(U2_ON_9), .A1N(ao_9), .A2N(U2_ON_9), .B1(ao_9), .B2(ai_9));

    // Stage 10

    AOI2BB2 U0_10 (.ON(ai_10), .A1N(ao_10), .A2N(U2_ON_10), .B1(ao_10), .B2(ri_10));
    AOI2BB2 U1_10 (.ON(ro_10), .A1N(ri_10), .A2N(U2_ON_10), .B1(ri_10), .B2(U2_ON_10));
    AOI2BB2 U2_10 (.ON(U2_ON_10), .A1N(ao_10), .A2N(U2_ON_10), .B1(ao_10), .B2(ai_10));


    BUF ao_0_buff (.O(ao_0), .I(ai_1) ); // stage 0 <- stage 1
    BUF ri_1_buff (.O(ri_1), .I(ro_0) ); // stage 0 -> stage 1

    BUF ao_1_buff (.O(ao_1), .I(ai_2) ); // stage 1 <- stage 2
    BUF ri_2_buff (.O(ri_2), .I(ro_1) ); // stage 1 -> stage 2

    BUF ao_2_buff (.O(ao_2), .I(ai_3) ); // stage 2 <- stage 3
    BUF ri_3_buff (.O(ri_3), .I(ro_2) ); // stage 2 -> stage 3

    BUF ao_3_buff (.O(ao_3), .I(ai_4) ); // stage 3 <- stage 4
    BUF ri_4_buff (.O(ri_4), .I(ro_3) ); // stage 3 -> stage 4

    BUF ao_4_buff (.O(ao_4), .I(ai_5) ); // stage 4 <- stage 5
    BUF ri_5_buff (.O(ri_5), .I(ro_4) ); // stage 4 -> stage 5

    BUF ao_5_buff (.O(ao_5), .I(ai_6) ); // stage 5 <- stage 6
    BUF ri_6_buff (.O(ri_6), .I(ro_5) ); // stage 5 -> stage 6

    BUF ao_6_buff (.O(ao_6), .I(ai_7) ); // stage 6 <- stage 7
    BUF ri_7_buff (.O(ri_7), .I(ro_6) ); // stage 6 -> stage 7

    BUF ao_7_buff (.O(ao_7), .I(ai_8) ); // stage 7 <- stage 8
    BUF ri_8_buff (.O(ri_8), .I(ro_7) ); // stage 7 -> stage 8

    BUF ao_8_buff (.O(ao_8), .I(ai_9) ); // stage 8 <- stage 9
    BUF ri_9_buff (.O(ri_9), .I(ro_8) ); // stage 8 -> stage 9

    BUF ao_9_buff (.O(ao_9), .I(ai_10) ); // stage 9 <- stage 10
    BUF ri_10_buff (.O(ri_10), .I(ro_9) ); // stage 9 -> stage 10


    // signal values at the initial state:
    // !ai_0 !ro_0 !U2_ON_0 !ao_0 !ri_0 !ai_1 !ro_1 !U2_ON_1 !ao_1 !ri_1 !ai_2 !ro_2 !U2_ON_2 !ao_2 !ri_2 !ai_3 !ro_3 !U2_ON_3 !ao_3 !ri_3 !ai_4 !ro_4 !U2_ON_4 !ao_4 !ri_4 !ai_5 !ro_5 !U2_ON_5 !ao_5 !ri_5 !ai_6 !ro_6 !U2_ON_6 !ao_6 !ri_6 !ai_7 !ro_7 !U2_ON_7 !ao_7 !ri_7 !ai_8 !ro_8 !U2_ON_8 !ao_8 !ri_8 !ai_9 !ro_9 !U2_ON_9 !ao_9 !ri_9 !ai_10 !ro_10 !U2_ON_10 !ao_10 !ri_10

    endmodule

