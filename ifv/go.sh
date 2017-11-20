#!/bin/bash

export PATH=$PATH:/eda/cadence/old/0910/IFV_8.2HF014/tools/bin

PROJECT_DIR=$(pwd)
DESIGN_DIR=$PROJECT_DIR/generated
EXAMPLE_DIR=$PROJECT_DIR/examples
WORK_DIR=$PROJECT_DIR/workspace
GATE_DIR=$PROJECT_DIR/gates

rm -f $EXAMPLE_DIR/*.vcd
rm -rf $WORK_DIR

mkdir $WORK_DIR && cd $WORK_DIR

ifv \
	$DESIGN_DIR/circuit.v \
	$DESIGN_DIR/spec.v \
	$GATE_DIR/*.v \
	+tcl+$PROJECT_DIR/run.tcl \
	+top+circuit \
	+64bit \
	+bind_top+bind_info \
	+nocopyright \
	-q \
	# +gui

simvisdbutil -vcd $WORK_DIR/examples -output $EXAMPLE_DIR/counter.vcd -overwrite >/dev/null 2>&1
