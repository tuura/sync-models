// vi: set ft=verilog :

{%- set inputs = spec["inputs"] %}
{%- set outputs = spec["outputs"] %}
{%- set initial = spec["initial_state"] %}
{%- set ena_bits = circuit["initial_state"]|length %}
{%- set transitions = spec["transitions"]|sort %}

`define clk_rst @(posedge clk) disable iff (reset)

module spec (reset, clk, ena, {{ (inputs+outputs)|join(', ')}});

    input reset, clk;
    input [{{ena_bits-1}}:0] ena;

    input {{ inputs  | join(', ') }};
    input {{ outputs | join(', ') }};

    // enable signal constraint

    wire [{{ ena_bits-1 }}:0] ena;

    ena_onehot : assume property ( `clk_rst $onehot0(ena) );

    // model (derived from sg)

    integer state;

    always @(posedge clk or posedge reset) begin

        if (reset) begin

            {%- set initial_ind = state_inds[initial] %}

            state <= {{ initial_ind }};

        end else begin

            {%- for from, tr, to in transitions %}

            {%- set signal = tr[:-1] %}
            {%- set sign = tr[-1] %}

            {%- set from_ind = state_inds[from] %}
            {%- set to_ind = state_inds[to] %}

            {%- set verilog_tr = ("~" + signal) if sign == "-" else signal %}
            if (state == {{ from_ind }} && {{ verilog_tr }} ) state <= {{ to_ind }};
            {%- endfor %}

        end

    end

    // Properties

    {%- for signal in inputs + outputs %}

    {%- set rise_tr = signal + "+" %}
    {%- set fall_tr = signal + "-" %}

    wire {{ signal }}_can_fall = 0
        {%- for prior, tr, _ in transitions if tr == fall_tr %}
        {%- set prior_ind = state_inds[prior] %}
        {{ "|| (state == %d)"|format(prior_ind) }}
        {%- endfor %}
        ;

    wire {{ signal }}_can_rise = 0
        {%- for prior, tr, _ in transitions if tr == rise_tr %}
        {%- set prior_ind = state_inds[prior] %}
        {{ "|| (state == %d)"|format(prior_ind) }}
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

module bind_info();

bind circuit spec u1 (
          .reset(reset)
        , .clk(clk)
        , .ena(ena)
        {%- for signal in inputs+outputs %}
        , .{{signal}}({{ signal }})
        {%- endfor %}
    );

endmodule
