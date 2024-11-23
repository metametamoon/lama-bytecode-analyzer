# TESTS=$(sort $(basename $(wildcard tests/test*.lama)))
T1=$(sort $(basename $(wildcard tests/*.lama)))
TESTS=$(notdir $(T1))

build/analyzer: src/main.cpp src/bytefile.cpp
	mkdir -p build
	g++ -m32 -g2 -fstack-protector-all -Wall -Werror -Wno-unused-variable src/main.cpp src/bytefile.cpp -o build/analyzer


.PHONY: test $(TESTS)


test: build/analyzer
	@echo $(TESTS)
	@echo $(T1)
	build/analyzer bytecodes/test09.bc



$(TESTS): %: build/analyzer
	@echo $@
	lamac -b tests/$@.lama
	byterun $@.bc > bytecodes/$@.dis
	mv $@.bc bytecodes/$@.bc
	build/analyzer bytecodes/$@.bc