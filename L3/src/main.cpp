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
#include "tile.h"

using namespace std;

vector<string> L3::caller_save_registers = {
        "r10", "r11", "r8", "r9", "rax", "rcx", "rdi", "rdx", "rsi"
};

vector<string> L3::arg_registers = {
        "rdi", "rsi", "rdx", "rcx", "r8", "r9"
};

vector<string> L3::callee_save_registers = {
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

  ofstream output;
  output.open("prog.L2");

  // parse program
  L3::Program p = L3::L3_parse_file(argv[optind]);

  output << "(:main\n";

  // generate trees
  for (auto fun : p.functions) {
    output << "(" << fun->name << endl;
    string fun_id = fun->name.erase(0, 1) + "uniqid";
    output << fun->args.size() << " 0\n";
    vector<shared_ptr<tree::Tree>> forest = generate_forest(*fun, fun_id);
    forest = merge_forest(forest);

    // tile the trees
    vector<vector<shared_ptr<tile::Tile>>> tiles = tile_forest(forest);

    // generate the output
    for (auto tiling : tiles)
      for (auto i = tiling.size(); i > 0; i--)
        for (auto i_str : tiling[i - 1]->dump_instructions())
          output << i_str << endl;

    output << ")\n";
  }

  output << ")\n";
  return 0;
}
