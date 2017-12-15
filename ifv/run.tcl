# clear

# Initialization

reset

# clock -add clk1 -width 1 -period 2
# clock -add clk2 -width 1 -period 2
# clock -add clk3 -width 1 -period 2
clock -add clk -width 1 -period 2

force reset 0
run 2
force reset 1
run 2

clock -show

# The supported values are 'Auto', 'Axe', 'Axe1', 'Axe2', 'Sword', 'Sword1',
# 'Sword2', 'Bow', 'Bow1', 'Bow2', 'Bow3', 'Hammer', 'Hammer1', 'Spear',
# 'Spear1', 'Spear2'.

# define engine hammer

init -load -current

# init -show

constraint -add -pin reset 0 -reset

# Attempt prove and save counter-examples

define effort 5 minutes
define delay_assertion 2

# Disable design partitioning algorithm. This cuts down the verification test
# of the incorrect arbiter circuit (with tied inputs optimization) fom 30 down
# to 20 seconds.
define halo off

# brings it down to 16
define witness_check off

report

# exit

# check -show

prove

# debug system.no_multiple_grants -sstexport examples -overwrite
debug u1.deadlock_free -sstexport examples -overwrite

exit
