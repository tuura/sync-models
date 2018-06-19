## Synchronous Model Generation Tool

### Overview

This repository contains a tool for converting asynchronous circuits into
equivalent synchronous models.

The models can be used as drop-in replacements for async circuits in
conventional (sync) simulation and formal verification, enabling users to
leverage existing (sync) tools, design flows, formalisms and knowledge to
simulate and verify async circuits.

Generated circuits have the same interface as input circuits but with added
`clk` and `reset` pins.

### Paper and Talk Slides

For more information on the tool please refer to:

- The paper [Formal Verification of Mixed Synchronous Asynchronous Systems using
Industrial Tools](https://github.com/tuura/sync-models-paper)

- The accompanying [presentation
slides](https://tuura.github.io/sync-models-paper/slides/)

### Documentation

- [User Manual](./doc/manual.md)
- [Tutorial](./doc/tutorial.md)
- [Support Tools](./doc/support-tools.md)
