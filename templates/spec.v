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

            state <= {{ initial }};

        end else begin

            {%- for from, tr, to in transitions %}
            if (state == {{ from }} && {{ tr}} ) state <= {{ to }};
            {%- endfor %}

        end

    end

    // Properties

    {%- for _, tr, _ in transitions %}

    {%- set prefix = tr[0] %}
    {%- set signal = tr[1:] %}
    {%- set tr_ena_signal = signal + ("_can_fall" if prefix=="~" else "_can_rise") %}

    wire {{ tr_ena_signal }} = 0
        {%- for prior, tr2, _ in transitions if tr == tr2 %}
        {{ "|| (state == %s)"|format(prior) }}
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
