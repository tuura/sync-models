TEMP_G="temp.g"

run:
	python generate.py 4 > $TEMP_G
	petrify -huge -write_sg $TEMP_G > "spec.sg"
	petrify \
		-tm \
		-lib c:\bin\workcraft\libraries\workcraft.lib \
		-vl circuit.v \
		$TEMP_G
	rm -rf $TEMP_G petrify.log


