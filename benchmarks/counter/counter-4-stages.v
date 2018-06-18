
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

        AOI2BB2 U0_3 (.ON(ai_3), .A1N(ao), .A2N(U2_ON_3), .B1(ao), .B2(ri_3));
        AOI2BB2 U1_3 (.ON(ro), .A1N(ri_3), .A2N(U2_ON_3), .B1(ri_3), .B2(U2_ON_3));
        AOI2BB2 U2_3 (.ON(U2_ON_3), .A1N(ao), .A2N(U2_ON_3), .B1(ao), .B2(ai_3));

    BUF ao_0_buf (.O(ao_0), .I(ai_1)); // stage 0 <- stage 1
    BUF ri_1_buf (.O(ri_1), .I(ro_0)); // stage 0 -> stage 1

    BUF ao_1_buf (.O(ao_1), .I(ai_2)); // stage 1 <- stage 2
    BUF ri_2_buf (.O(ri_2), .I(ro_1)); // stage 1 -> stage 2

    BUF ao_2_buf (.O(ao_2), .I(ai_3)); // stage 2 <- stage 3
    BUF ri_3_buf (.O(ri_3), .I(ro_2)); // stage 2 -> stage 3

    // signal values at the initial state:
    // !ai !ro_0 !U2_ON_0 !ao_0 !ri !ai_1 !ro_1 !U2_ON_1 !ao_1 !ri_1 !ai_2 !ro_2 !U2_ON_2 !ao_2 !ri_2 !ai_3 !ro !U2_ON_3 !ao !ri_3

    endmodule
    
