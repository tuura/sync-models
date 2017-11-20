// vi: set ft=verilog :

{%- set inputs = spec["inputs"]|sort %}
{%- set outputs = spec["outputs"]|sort %}
{%- set ntransitions = initial_state|length %}

module circuit (
          input reset
        , input clk
        {{- ", det" if dbits -}}

        {%- for input in inputs|sort %}
        , input {{ input }}_precap // input
        {%- endfor %}

        {%- for input in outputs|sort %}
        , output {{ input }} // output
        {%- endfor %}
    );

	reg [{{bit_size(ntransitions)-1}}:0] fire; // unbound register

	{%- for input in inputs %}

	{% set initial_value = initial_state[input] -%}

	// input signal '{{input}}' (initial value = {{initial_value}})

	DFF {{input}}_ff (
		.CK(clk),
		.ST({{ "reset" if     initial_value else "1'b0" }}),
		.RS({{ "reset" if not initial_value else "1'b0" }}),
		.D({{input}}_precap),
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
	); {{"// virtual module" if mod.get("virtual")}}

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
		.PRECAP({{output_pre}}),

		{%- for pin, net in mod["connections"].iteritems() %}
		.{{pin}}({{net}}),
		{%- endfor %}
		.ENA(fire == {{fire_ind}})
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
