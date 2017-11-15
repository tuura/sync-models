run: prepare_output
	@ python generator.py \
	>> output.log 2>&1

prepare_output:
	@ date > output.log
	@ date | sed 's/./#/g' >> output.log
	@ echo "" >> output.log
