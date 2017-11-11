// vi: set ft=verilog :

{%- set inputs = spec["inputs"] %}
{%- set outputs = spec["outputs"] %}
{%- set ena_bits = circuit["modules"]|length + inputs|length %}

module circuit (reset, clk, ena, {{ (inputs+outputs)|join(', ')}});

	input reset, clk;
	input [{{ena_bits-1}}:0] ena;

	output {{ inputs  | join(', ') }};
	output {{ outputs | join(', ') }};

	{%- for input in inputs %}

	{% set initial_value = circuit["initial_state"][input] -%}

	// signal '{{input}}' (initial value = {{ initial_value }})

	DFF {{input}}_ff (
		.CK(clk),
		.RS({{ "reset" if initial_value else "1'b0"  }}),
		.ST({{ "1'b0"  if initial_value else "reset" }}),
		.D(~{{input}}),
		.Q({{input}}),
		.ENA(ena[{{loop.index0}}])
	);

	{%- endfor -%}

	{% for instance, gate in circuit["modules"].iteritems() %}

	{%- set output_pin = lib[gate["type"]]["output"] -%}
	{%- set output_net = gate["connections"][output_pin] -%}
	{% set initial_value = circuit["initial_state"][output_net] %}

	// signal '{{output_net}}' (initial value = {{ initial_value }})

	{%- if lib[gate["type"]]["type"] == "GATE" %}

	{{gate["type"]}} {{instance}} (

		{%- for pin, net in gate["connections"].iteritems() %}
		{%- if pin == output_pin %}
		.{{pin}}({{net}}_precap){{ "," if not loop.last }}
		{%- else %}
		.{{pin}}({{net}}){{ "," if not loop.last }}
		{%- endif %}

		{%- endfor %}
	);

	{%- set output_net = gate["connections"][output_pin] %}

	DFF {{instance}}_ff (
		.CK(clk),
		.RS({{ "1'b0"  if initial_value else "reset" }}),
		.ST({{ "reset" if initial_value else "1'b0"  }}),
		.D({{output_net}}_precap),
		.Q({{output_net}}),
		.ENA(ena[{{ loop.index0 + inputs|length }}])
	);

	{%- else %}

	{{gate["type"]}} {{instance}} (
		.CK(clk),
		.RS({{ "1'b0"  if initial_value else "reset" }}),
		.ST({{ "reset" if initial_value else "1'b0"  }}),

		{%- for pin, net in gate["connections"].iteritems() %}
		{%- if pin == output_pin %}
		.{{pin}}({{net}}){{ "," if not loop.last }}
		{%- else %}
		.{{pin}}({{net}}){{ "," if not loop.last }}
		{%- endif %}

		{%- endfor %}
	);

	{%- endif %}

	{%- endfor %}

endmodule
