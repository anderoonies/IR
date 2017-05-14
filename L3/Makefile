CPP_FILES := $(wildcard src/*.cpp)
OBJ_FILES := $(addprefix obj/,$(notdir $(CPP_FILES:.cpp=.o)))
CC_FLAGS  := --std=c++11 -I./src -I../lib/PEGTL -I../lib -g3
LD_FLAGS  := 
CC        := g++

all: obj bin L3

obj:
	mkdir -p $@

bin:
	mkdir -p $@

L3: $(OBJ_FILES)
	$(CC) $(LD_FLAGS) -o ./bin/$@ $^

obj/%.o: src/%.cpp
	$(CC) $(CC_FLAGS) -c -o $@ $<

oracle: L3
	../scripts/generateOutput.sh $^ L3c

rm_tests_without_oracle:
	../scripts/rm_tests_without_oracle.sh L3

test: L3
	./scripts/test.sh

clean:
	rm -fr bin obj *.out *.L2 *.o *.S core.* tests/liveness/*.tmp tests/*.tmp
