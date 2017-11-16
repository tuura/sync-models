// vi: set ft=verilog :

{%- set inputs = spec["inputs"] %}
{%- set outputs = spec["outputs"] %}
{%- set ntransitions = initial_state|length %}

module circuit (
          input reset
        , input clk
        , input [{{bit_size(ntransitions)-1}}:0] fire
        {{- ", det" if dbits -}}

        {%- for input in inputs|sort %}
        , output {{ input }} // input
        {%- endfor %}

        {%- for input in outputs|sort %}
        , output {{ input }} // output
        {%- endfor %}
    );

	{%- for input in inputs %}

	{% set initial_value = initial_state[input] -%}

	// input signal '{{input}}' (initial value = {{initial_value}})

	DFF {{input}}_ff (
		.CK(clk),
		.ST({{ "reset" if     initial_value else "1'b0" }}),
		.RS({{ "reset" if not initial_value else "1'b0" }}),
		.D(~{{input}}),
		.Q({{input}}),
		.ENA(fire == {{loop.index0}})
	);

	{%- endfor -%}

	{#-------- Stateful Modules --------#}

	{% for instance, mod in stateful.iteritems() %}

	{%- set output_pin = lib[mod["type"]]["output"] -%}
	{%- set output_net = mod["connections"][output_pin] -%}
	{%- set category = "output" if output_net in outputs else "internal" -%}
	{% set initial_value = initial_state[output_net] %}

	// {{category}} signal '{{output_net}}' (initial value = {{initial_value}})

	{%- if lib[mod["type"]]["type"] == "GATE" %}

	{#-------- Gate --------#}

	{%- set output_net = mod["connections"][output_pin] %}
	{%- set output_pre = output_net + "_precap" %}
	{%- set fire_ind = loop.index0 + inputs|length %}

	{{mod["type"]}} {{instance}} (

		{%- for pin, net in mod["connections"].iteritems() %}
		{%- set pin_net = output_pre if pin==output_pin else net -%}
		.{{pin}}({{pin_net}}){{ ", " if not loop.last }}
		{%- endfor -%}
	);

	DFF {{instance}}_ff (
		.CK(clk),
		.ST({{ "reset" if     initial_value else "1'b0" }}),
		.RS({{ "reset" if not initial_value else "1'b0" }}),
		.D({{output_pre}}),
		.Q({{output_net}}),
		.ENA(fire == {{fire_ind}})
	);

	{#-------- End of Gate --------#}

	{%- else %}

	{#-------- Latch --------#}

	{%- set output_net = mod["connections"][output_pin] %}
	{%- set fire_ind = loop.index0 + inputs|length %}
	{%- set output_pre = output_net + "_precap" %}

	{{mod["type"]}} {{instance}} (
		.CK(clk),
		.RS({{ "reset" if not initial_value else "1'b0" }}),
		.ST({{ "reset" if     initial_value else "1'b0" }}),
		.ENA(fire == {{fire_ind}}),
		.PRECAP({{output_pre}}),

		{%- for pin, net in mod["connections"].iteritems() %}
		.{{pin}}({{net}}){{ "," if not loop.last }}
		{%- endfor %}
	);

	{#-------- End of Latch --------#}

	{%- endif %}

	{%- endfor %}

	{#-------- End of Stateful Modules -------- #}

	// Stateless modules

	{#-------- Non-stateful Modules --------#}

	{% for instance, mod in stateless.iteritems() %}

	{% set output_pin = lib[mod["type"]]["output"] -%}
	{%- set output_net = mod["connections"][output_pin] -%}

	{{mod["type"]}} {{instance}} (

		{%- for pin, net in mod["connections"].iteritems() -%}
		.{{pin}}({{net}}){{ ", " if not loop.last }}
		{%- endfor -%}
	);

	{%- endfor -%}

	{#-------- End of non-stateful Modules -------- #}

endmodule
