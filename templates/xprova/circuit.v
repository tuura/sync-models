// vi: set ft=verilog :

// ---- Xprova properties ----

{%- set ntransitions = nets|length %}

// Assumptions (spec compliance):
{% for input in inputs %}
assume $rose({{input}}) |-> @1 {{input}}_can_rise
assume $fell({{input}}) |-> @1 {{input}}_can_fall
{%- endfor %}

// Assertions (spec compliance):
{% for output in outputs %}
assert $rose({{output}}) |-> @1 {{output}}_can_rise
assert $fell({{output}}) |-> @1 {{output}}_can_fall
{%- endfor %}

// Output Persistency Properties (internals must be removed)
{% for net in stateful_nets %}
assert $fell({{net}}_ena) |-> $changed({{net}})
{%- endfor %}

assume fire <= {{ntransitions}}

assert exist_enabled_transition

// Transition firing assumptions:

{% for input in inputs %}
{%- set pre_net = input + "_precap" %}
{%- set fire_ind = loop.index0 -%}
assume (fire == {{fire_ind}}) |-> ({{input}} ^ {{pre_net}})
{% endfor -%}

{% for net in stateful_nets %}
{%- set fire_ind = loop.index0 + inputs|length -%}
assume (fire == {{fire_ind}}) |-> ({{net}} ^ {{net}}_precap)
{% endfor %}
// ---- end of Xprova properties ----

`include "workcraft.v"
`include "gates.v"
`include "builtins.v"

module circuit (
		input reset,
		input clk,
		input [{{firebits-1}}:0] fire,
		{{- "det," if dbits -}}

		{%- for input in inputs %}
		input {{ input }}_precap, // input
		{%- endfor %}

		{%- for input in outputs %}
		output {{ input }}, // output
		{%- endfor %}

		{%- for signal in inputs+outputs %}
		output {{ signal }}_can_fall,
		output {{ signal }}_can_rise,
		{%- endfor %}
		output exist_enabled_transition,

		{%- for signal in nets %}
		output {{signal}}_ena,
		{%- endfor %}

		{%- for signal in nets -%}
		{%- if signal not in inputs %}
		output {{signal}}_precap,
		{%- endif -%}
		{%- endfor %}
	);


	{%- for input in inputs %}

	{% set initial_value = initial_circuit[input] -%}

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

	{%- set output_pin = get_output_pin(mod) -%}
	{%- set output_net = get_output_net(mod) -%}
	{%- set output_pre = output_net + "_precap" %}
	{%- set category = "output" if output_net in outputs else "internal" -%}
	{% set initial_value = initial_circuit[output_net] -%}
	{% set fire_ind = firing_indices[output_net] %}

	// {{category}} signal '{{output_net}}' (initial value = {{initial_value}})

	{%- if lib[mod["type"]]["type"] == "GATE" %}

	{#-------- Gate -------- #}

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

	{#-------- Latch -------- #}

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

	{%- set output_net = get_output_net(mod) -%}

	{{mod["type"]}} {{instance}} (

		{%- for pin, net in mod["connections"].iteritems() -%}
		.{{pin}}({{net}}){{ ", " if not loop.last }}
		{%- endfor -%}
	);

	{%- endfor -%}

	{#-------- End of non-stateful Modules -------- #}

	// spec

	integer state;

	always @(posedge clk or posedge reset) begin

	    if (reset) begin

	        {%- set initial_ind = state_inds[initial_spec] %}

	        state <= {{ initial_ind }}; // {{ initial_spec }}

	    end else begin
	        {% for from, tr, to in transitions -%}
	        {%- set signal     = tr[:-1]          -%}
	        {%- set sign       = tr[-1]           -%}
	        {%- set from_ind   = state_inds[from] -%}
	        {%- set to_ind     = state_inds[to]   -%}
	        {%- set fire_ind = firing_indices[signal] -%}
	        {%- set verilog_tr = ("~" + signal) if sign == "-" else signal %}
	        if (state == {{ from_ind }} && {{ verilog_tr }}_precap && fire == {{fire_ind}}) state <= {{ to_ind }};  // {{ to }}
	        {%- endfor %}

	    end

	end

	// Spec Compliance Properties:

	{%- for signal in inputs + outputs %}

	wire {{ signal }}_can_fall = 0
	    {%- for prior, tr, _ in transitions if tr == signal + "-" %}
	    {%- set prior_ind = state_inds[prior] %}
	    {{ "|| (state == %d)"|format(prior_ind) }}
	    {%- endfor -%}
	    ;

	wire {{ signal }}_can_rise = 0
	    {%- for prior, tr, _ in transitions if tr == signal + "+" %}
	    {%- set prior_ind = state_inds[prior] %}
	    {{ "|| (state == %d)"|format(prior_ind) }}
	    {%- endfor -%}
	    ;

	{%- endfor %}


	// Enable signals:

	// Note: while internal transition enable status are indicated by (net ^
	// net_precap), inputs are generated by the environment and may therefore
	// may be enabled wile the expression (input ^ input_precap) is false.
	// Input enable status must therefore be derived from the spec, as
	// input_can_rise | input_can_fall.

	{% for input in inputs %}
	assign {{input}}_ena = {{input}}_can_rise | {{input}}_can_fall;
	{%- endfor -%}
	{%- for net in stateful_nets %}
	assign {{net}}_ena = {{net}}_precap ^ {{net}};
	{%- endfor %}

	// Deadlock

	// Deadlock freeness: on each cycle, at least one transition is enabled.

	assign exist_enabled_transition =
	    {%- for input in inputs %}
	    | {{input}}_ena
	    {%- endfor -%}
	    {%- for net in stateful_nets %}
	    | {{net}}_ena
	    {%- endfor -%}
	;

endmodule
