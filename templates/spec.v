// vi: set ft=verilog :

{%- set inputs = spec["inputs"] %}
{%- set outputs = spec["outputs"] %}
{%- set initial = spec["initial_state"] %}
{%- set transitions = spec["transitions"]|sort %}
{%- set ntransitions = (inputs+stateful.values())|length %}

`define clk_rst @(posedge clk) disable iff (reset)

module spec (reset, clk, fire, {{ "det, " if dbits -}} {{ (inputs+outputs)|join(', ')}} );

    input reset, clk;
    input [{{bit_size(ntransitions)-1}}:0] fire;

    {%- if dbits -%}
        {%- if dbits > 1 %}
    input [{{dbits-1}}:0] det;
        {%- elif dbits == 1 %}
    input det;
        {%- endif -%}
    {%- endif %}

    input {{ inputs  | join(', ') }};
    input {{ outputs | join(', ') }};

    // fire signal constraints

    reg [{{bit_size(ntransitions)-1}}:0] fire_ne;  // fire, sampled on negedge

    always @(negedge clk) fire_ne = fire;

    // Note:
    // - fire = [0, {{ntransitions}}] -> transition #fire is enabled
    // - fire = {{ntransitions+1}} -> all transitions are disabled

    ena_in_range : assume property ( `clk_rst fire <= {{ntransitions + 1}} );

    ena_cycle_stable : assume property(`clk_rst fire == fire_ne);

    // model (derived from sg)

    integer state;

    always @(posedge clk or posedge reset) begin

        if (reset) begin

            {%- set initial_ind = state_inds[initial] %}

            state <= {{ initial_ind }}; // {{ initial }}

        end else begin
            {% for from, tr, to in transitions -%}
            {%- set signal = tr[:-1] -%}
            {%- set sign = tr[-1] -%}
            {%- set from_ind = state_inds[from] -%}
            {%- set to_ind = state_inds[to] -%}
            {%- set verilog_tr = ("~" + signal) if sign == "-" else signal %}
            if (state == {{ from_ind }} && {{ verilog_tr }} ) state <= {{ to_ind }};  // {{ to }}
            {%- endfor %}

        end

    end

    // Spec Compliance Properties:

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
        , .fire(fire)
        {%- for signal in inputs+outputs %}
        , .{{signal}}({{ signal }})
        {%- endfor %}
    );

endmodule
