
    module Untitled(ri, ro, ai, ao);

    input ri, ao;
    output ro, ai;

    // Stage 0

    AOI2BB2 U0_0 (.ON(ai), .A1N(ao_0), .A2N(U2_ON_0), .B1(ao_0), .B2(ri));
    AOI2BB2 U1_0 (.ON(ro_0), .A1N(ri), .A2N(U2_ON_0), .B1(ri), .B2(U2_ON_0));
    AOI2BB2 U2_0 (.ON(U2_ON_0), .A1N(ao_0), .A2N(U2_ON_0), .B1(ao_0), .B2(ai));

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

    AOI2BB2 U0_7 (.ON(ai_7), .A1N(ao), .A2N(U2_ON_7), .B1(ao), .B2(ri_7));
    AOI2BB2 U1_7 (.ON(ro), .A1N(ri_7), .A2N(U2_ON_7), .B1(ri_7), .B2(U2_ON_7));
    AOI2BB2 U2_7 (.ON(U2_ON_7), .A1N(ao), .A2N(U2_ON_7), .B1(ao), .B2(ai_7));

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

    // signal values at the initial state:
    // !ai !ro_0 !U2_ON_0 !ao_0 !ri !ai_1 !ro_1 !U2_ON_1 !ao_1 !ri_1 !ai_2 !ro_2 !U2_ON_2 !ao_2 !ri_2 !ai_3 !ro_3 !U2_ON_3 !ao_3 !ri_3 !ai_4 !ro_4 !U2_ON_4 !ao_4 !ri_4 !ai_5 !ro_5 !U2_ON_5 !ao_5 !ri_5 !ai_6 !ro_6 !U2_ON_6 !ao_6 !ri_6 !ai_7 !ro !U2_ON_7 !ao !ri_7

    endmodule

