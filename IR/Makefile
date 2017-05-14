CPP_FILES := $(wildcard src/*.cpp)
OBJ_FILES := $(addprefix obj/,$(notdir $(CPP_FILES:.cpp=.o)))
CC_FLAGS  := --std=c++11 -I./src -I../lib/PEGTL -I../lib -g3
LD_FLAGS  := 
CC        := g++

all: dirs IR

dirs: obj bin

obj:
	mkdir -p $@

bin:
	mkdir -p $@

IR: $(OBJ_FILES)
	$(CC) $(LD_FLAGS) -o ./bin/$@ $^

obj/%.o: src/%.cpp
	$(CC) $(CC_FLAGS) -c -o $@ $<

oracle: IR
	../scripts/generateOutput.sh $^ IRc

rm_tests_without_oracle:
	../scripts/rm_tests_without_oracle.sh IR

test: dirs IR
	./scripts/test.sh

clean:
	rm -fr bin obj *.out *.L3 *.o *.S core.* tests/liveness/*.tmp tests/*.tmp
