#include <string>
#include <vector>
#include <utility>
#include <algorithm>
#include <set>
#include <iterator>
#include <iostream>
#include <cstring>
#include <cctype>
#include <cstdlib>
#include <stdint.h>
#include <unistd.h>
#include <iostream>
#include <fstream>
#include <map>

// my stuff
#include "parser.h"
#include "compiler.h"
#include "../../L3/src/L3.h"

using namespace std;

vector<string> IR::caller_save_registers = {
        "r10", "r11", "r8", "r9", "rax", "rcx", "rdi", "rdx", "rsi"
};

vector<string> IR::arg_registers = {
        "rdi", "rsi", "rdx", "rcx", "r8", "r9"
};

vector<string> IR::callee_save_registers = {
        "r12", "r13", "r14", "r15", "rbp", "rbx"
};

int main( int argc, char **argv ){
  bool verbose;

  /* Check the input.
   */
  if( argc < 2 ) {
    std::cerr << "Usage: " << argv[ 0 ] << " SOURCE [-v]" << std::endl;
    return 1;
  }
  int32_t opt;
  while ((opt = getopt(argc, argv, "v")) != -1) {
    switch (opt){
      case 'v':
        verbose = true;
        break ;

      default:
        std::cerr << "Usage: " << argv[ 0 ] << "[-v] SOURCE" << std::endl;
        return 1;
    }
  }

  // parse program
  IR::Program p = IR::IR_parse_file(argv[optind]);
  // compile and dump it to the outfile
  Compiler::Compile(p);

  return 0;
}
