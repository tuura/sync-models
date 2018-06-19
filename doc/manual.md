### User Manual

The main tool is `generator.py`, a Verilog code generator based on
[Jinja](http://jinja.pocoo.org).

#### Usage

```
Usage:
  generator.py [options] <circuit.v>

Options:
  -o --output=<dir>         Write output files to directory.
  -s --spec=<spec.sg>       Generate spec model for verification.
  -t --template=<template>  Specify template [default: standard].
  -l --lib=<dir>            Load additional library file(s).
```

where the input circuit `circuit.v` is a gate-level Verilog netlist.

By default, the tool will print the generated circuit to the terminal. If
`--output <dir>` is supplied, the tool will save the generated file to the
directory `<dir>`.

#### Libraries

The tool ships with two library files (inside `libraries`). These files are
used for two purposes. First, they are used by the tool itself to read input
circuits. Second, they contain definitions for cells inside the generated sync
model (and must therefore be imported by sync simulators/verifiers that use
the generated circuit).

The tool can load additional (user) library files using `--lib`.

#### Templates

The tool relies on code _templates_ to generated models. The `standard`
template is stable and used by default. Two other templates are provided but
are mainly used for research purposes.

#### Specification Models

In addition to the circuit itself, the tool is capable of generating a
specification model based on a Signal Transition file. The specification model
can be used by sync verifiers to check that the circuit complies with its
specification.

To generate a specification model, run the tool as follows:

```
./generator.py --spec myspec.sg --output generated circuit.v
```

The tool generates both circuit and spec models when `--spec` is used. It is
therefore best to accompany this with `--output` to write generated files to a
given directory instead of printing them to the terminal.
