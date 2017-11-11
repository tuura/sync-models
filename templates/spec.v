
`define clk_rst @(posedge clk) disable iff (reset)

module spec (
          input reset
        , input clk
        , input ena
        {%- for signal in signals %}
        , input {{ signal }}
        {%- endfor %}
    );

    // enable signal constraint

    wire [{{ ena_bits }}-1:0] ena;

    ena_onehot : assume property ( `clk_rst $onehot0(ena) );

    // model (derived from sg)

    reg [{{ state_bits }}-1:0] state;

    always @(posedge clk or posedge reset) begin

        if (reset) begin

            state <= {{ initial }};

        end else begin

            {%- for from, tr, to in transitions %}
            if (state == {{ from }} && {{ tr}} ) state <= {{ to }};
            {%- endfor %}

        end

    end

    // Properties

    {%- for tr, states in valid_states.iteritems() %}

    wire {{ can_transition[tr] }} = 0
        {%- for state in states %}
        || (state == {{ state }})
        {%- endfor %}
    ;

    {%- endfor %}

    // Assumptions
    {% for input in inputs %}
    {{input}}_rise: assume property ( `clk_rst $rose({{input}}) |-> {{input}}_can_rise );
    {{input}}_fall: assume property ( `clk_rst $fell({{input}}) |-> {{input}}_can_fall );
    {%- endfor %}

    // Assertions
    {% for output in outputs %}
    {{output}}_rise: assert property ( `clk_rst $rose({{output}}) |-> {{output}}_can_rise );
    {{output}}_fall: assert property ( `clk_rst $fell({{output}}) |-> {{output}}_can_fall );
    {%- endfor %}

endmodule
