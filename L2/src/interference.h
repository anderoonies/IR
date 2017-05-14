#include <vector>
#include <string>
#include <set>
#include <iostream>
#include <map>
#include "L2.h"

using namespace std;

namespace Analysis {

  // represent adjacencies using a data structure which does not change
  // during execution of the algorithm. this is used only for lookups
  // and is not modified when something is spilled.
  extern std::map<string, std::set<string>> adjacencies;

  extern std::set<std::string> variables;
  extern std::map<string, int> coloring;

  pair<map<string, int>, vector<string>>
    interference_analysis(
      std::vector<std::set<std::string>> in,
      std::vector<std::set<std::string>> out,
      std::vector<std::set<std::string>> kill,
      L2::Function *f);

  L2::Function *translate_to_L1(L2::Function *f, vector<string> stack);
  L2::Function *spill(L2::Function *f, string var, int n_spilled);
}
