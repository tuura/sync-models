clear

# Initialization

reset

clock -add clk -width 1 -period 1 -offset 0

force reset 1

run 4

init -load -current

init -show

constraint -add -pin reset 0 -reset

# Attempt prove and save counter-examples

define effort 5 minutes
define delay_assertion 2

prove

witness circuit.u1.gn_rise -sstexport examples -overwrite

exit
