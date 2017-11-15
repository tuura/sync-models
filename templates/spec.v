// vi: set ft=verilog :

{%- set inputs = spec["inputs"] %}
{%- set outputs = spec["outputs"] %}
{%- set initial = spec["initial_state"] %}
{%- set transitions = spec["transitions"]|sort %}
{%- set ntransitions = (inputs+stateful.values())|length %}

`define clk_rst @(posedge clk) disable iff (reset)

module spec (
          input reset
        , input clk
        , input [{{bit_size(ntransitions)-1}}:0] fire
        {{- ", det" if dbits -}}

        {% for input in inputs %}
        , input {{ input }} // input
        {%- endfor %}

        {%- for _, mod in stateful.iteritems() %}
        , input {{ get_output_net(mod) }} // {{"output" if get_output_net(mod) in outputs else "internal"}}
        , input {{ get_output_net(mod) }}_precap
        {%- endfor %}
    );

    {%- if dbits -%}
        {%- if dbits > 1 %}
    input [{{dbits-1}}:0] det;
        {%- elif dbits == 1 %}
    input det;
        {%- endif -%}
    {%- endif %}

    // fire signal constraints

    reg [{{bit_size(ntransitions)-1}}:0] fire_ne;  // fire, sampled on negedge

    always @(negedge clk) fire_ne = fire;

    // Note:
    // - fire = [0, {{ntransitions}}] -> transition #fire is enabled
    // - fire = {{ntransitions+1}} -> all transitions are disabled

    fire_in_range : assume property ( `clk_rst fire <= {{ntransitions + 1}} );

    fire_cycle_stable : assume property(`clk_rst fire == fire_ne);

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
        {%- endfor -%}
        ;

    wire {{ signal }}_can_rise = 0
        {%- for prior, tr, _ in transitions if tr == rise_tr %}
        {%- set prior_ind = state_inds[prior] %}
        {{ "|| (state == %d)"|format(prior_ind) }}
        {%- endfor -%}
        ;

    {%- endfor %}

    // Assumptions (spec compliance):
    {% for input in inputs %}
    {{input}}_rise: assume property ( `clk_rst $rose({{input}}) |-> {{input}}_can_rise );
    {{input}}_fall: assume property ( `clk_rst $fell({{input}}) |-> {{input}}_can_fall );
    {%- endfor %}

    // Assertions (spec compliance):
    {% for output in outputs %}
    {{output}}_rise: assert property ( `clk_rst $rose({{output}}) |-> {{output}}_can_rise );
    {{output}}_fall: assert property ( `clk_rst $fell({{output}}) |-> {{output}}_can_fall );
    {%- endfor %}

    // Output Persistency Properties:

    {%- for instance, gate in stateful.iteritems() %}

    {%- set output_pin = lib[gate["type"]]["output"] -%}
    {%- set output_net = gate["connections"][output_pin] -%}
    {%- set output_pre = output_net + "_precap" %}
    {%- set initial_value = initial_state[output_net] -%}
    {%- set fire_ind = loop.index0 + inputs|length %}

    assign {{output_net}}_ena = {{output_pre}} != {{output_net}};

    {{output_net}}_persistency: assert property ( `clk_rst {{output_net}}_ena |=> ({{output_net}}_ena || ~$stable({{output_net}})) );

    {%- endfor %}

endmodule

module bind_info();

bind circuit spec u1 (
          .reset(reset)
        , .clk(clk)
        , .fire(fire)

        {%- for input in inputs %}
        , .{{input}}({{ input }})
        {%- endfor %}


        {%- for _, mod in stateful.iteritems() %}
        , .{{ get_output_net(mod) }}({{ get_output_net(mod) }})
        , .{{ get_output_net(mod) }}_precap({{ get_output_net(mod) }}_precap)
        {%- endfor -%}

    );

endmodule
