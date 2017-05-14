CPP_FILES := $(wildcard src/*.cpp)
OBJ_FILES := $(addprefix obj/,$(notdir $(CPP_FILES:.cpp=.o)))
CC_FLAGS  := --std=c++11 -I./src -I../lib/PEGTL -I../lib -g3
LD_FLAGS  := 
CC        := g++

all: obj bin L1

obj:
	mkdir -p $@

bin:
	mkdir -p $@

L1: $(OBJ_FILES)
	$(CC) $(LD_FLAGS) -o ./bin/$@ $^

obj/%.o: src/%.cpp
	$(CC) $(CC_FLAGS) -c -o $@ $<

oracle: L1
	../scripts/generateOutput.sh $^ L1c

rm_tests_without_oracle:
	../scripts/rm_tests_without_oracle.sh L1

test: L1
	./scripts/test.sh

test2: L1
	./scripts/test2.sh

clean:
	rm -fr bin obj *.out *.o *.S core.* tests/*.tmp
