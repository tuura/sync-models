### Formal Verification Tool: ESSET

The repository contains a low-performance verification tool `esset.py`
referred to in the paper as the Exhaustive State Space Exploration Tool
(ESSET). It's a compliance checker used mainly to cross-validate verification
results with other tools.

#### Usage

```
Usage:
  esset.py [options] <circuit.v> <spec.sg>

Options:
  -q --quiet      Suppress printing state exploration details.
  -l --lib=<dir>  Load libraries from specific directory [default: libraries].
  ```
