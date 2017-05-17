// generates the interference graph for a function

#include "interference.h"
#include <iostream>
#include <algorithm>

using namespace std;

std::vector<std::string> x86_registers = {
 "rdx", "rcx", "r8", "r9", "rax", "r10",
 "r11", "r12", "r13", "r14", "r15", "rbp", "rbx", "rdi", "rsi"
};

std::vector<std::string> non_spill = {
 "rdx", "rcx", "r8", "r9", "rax", "r10",
 "r11", "r12", "r13", "r14", "r15", "rbp", "rbx", "rdi", "rsi", "rsp"
};

std::map<string, set<string>> Analysis::adjacencies;
std::set<std::string> Analysis::variables;
std::map<string, int> Analysis::coloring;
std::map<string, std::set<string>> graph;

void dump_graph() {
  for (auto n : graph) {
    cout << n.first << endl;
    for (auto neighb : n.second)
      cout << neighb << ", ";
    cout << endl << "-----" <<  endl;
  }
}

string get_var_name(string var_name) {
  char prefix = var_name[1];
  if (prefix == 'z')
    return "_az" + var_name;
  else
    prefix++;
  var_name[1] = prefix;
  return var_name;
}


L2::Load* generate_spill_load(string lhs_name, int64_t offset) {
  L2::Load *spill_load = new L2::Load();
  L2::MemoryReference stackref;
  L2::L2_x rsp;
  L2::L2_w lhs;
  rsp.name = "rsp";
  stackref.value = rsp;
  stackref.offset_int = (offset - 1) * 8;
  lhs.name = lhs_name;
  spill_load->lhs = lhs;
  spill_load->rhs = stackref;
  return spill_load;
}

L2::Store* generate_spill_store(string rhs_name, int64_t offset) {
  L2::Store *spill_store = new L2::Store();
  L2::MemoryReference stackref;
  L2::L2_x rsp;
  L2::L2_s rhs;
  rsp.name = "rsp";
  stackref.value = rsp;
  stackref.offset_int = (offset - 1) * 8;
  rhs.name = rhs_name;
  spill_store->rhs = rhs;
  spill_store->lhs = stackref;
  return spill_store;
}

L2::Instruction *replace_var(L2::Instruction *i, string var, string var_name) {
  if (L2::Load *load = dynamic_cast<L2::Load *>(i)) {
    if (load->lhs.name == var)
      load->lhs.name = var_name;
    if (load->rhs.value.name == var)
      load->rhs.value.name = var_name;
    return load;
  }
  else if (L2::Store *store = dynamic_cast<L2::Store *>(i)) {
    if (store->rhs.name == var)
      store->rhs.name = var_name;
    if (store->lhs.value.name == var)
      store->lhs.value.name = var_name;
    return store;
  }
  else if (L2::Assignment *assn = dynamic_cast<L2::Assignment *>(i)) {
    if (assn->lhs.name == var)
      assn->lhs.name = var_name;
    if (assn->rhs.name == var)
      assn->rhs.name = var_name;
    return assn;
  }
  else if (L2::ReturnCall *ret = dynamic_cast<L2::ReturnCall *>(i)) {
    return ret;
  }
  else if (L2::ArithmeticOperation *aop = dynamic_cast<L2::ArithmeticOperation *>(i)) {
    if (aop->lhs.name == var)
      aop->lhs.name = var_name;
    if (aop->rhs.name == var)
      aop->rhs.name =var_name;
    return aop;
  }
  else if (L2::MemoryArithmeticOperation *maop = dynamic_cast<L2::MemoryArithmeticOperation *>(i)) {
    if (maop->lhs.value.name == var)
      maop->lhs.value.name = var_name;
    if (maop->rhs.name == var)
      maop->rhs.name = var_name;
    return maop;
  }
  else if (L2::MemoryArithmeticOperation2 *maop = dynamic_cast<L2::MemoryArithmeticOperation2 *>(i)) {
    if (maop->lhs.name == var)
      maop->lhs.name = var_name;
    if (maop->rhs.value.name == var)
      maop->rhs.value.name = var_name;
    return maop;
  }
  else if (L2::ShiftOperation *sop = dynamic_cast<L2::ShiftOperation *>(i)) {
    if (sop->lhs.name == var)
      sop->lhs.name = var_name;
    if (sop->rhs.name == var)
      sop->rhs.name = var_name;
    return sop;
  }
  else if (L2::ComparisonOperation *comp = dynamic_cast<L2::ComparisonOperation *>(i)) {
    if (comp->lhs.name == var)
      comp->lhs.name = var_name;
    if (comp->cexp.lhs.name == var)
      comp->cexp.lhs.name = var_name;
    if (comp->cexp.rhs.name == var)
      comp->cexp.rhs.name = var_name;
    return comp;
  }
  else if (L2::RuntimeCall *rCall = dynamic_cast<L2::RuntimeCall *>(i)) {
    if (rCall->function_name.name == var)
      rCall->function_name.name = var_name;
    return rCall;
  }
  else if (L2::FunctionCall *fCall = dynamic_cast<L2::FunctionCall *>(i)) {
    if (fCall->function_name.name == var)
      fCall->function_name.name = var_name;
    return fCall;
  }
  else if (L2::Label *lbl = dynamic_cast<L2::Label *>(i)) {
    return lbl;
  }
  else if (L2::WawweOperation *wawwe = dynamic_cast<L2::WawweOperation *>(i)) {
    if (wawwe->lhs.name == var)
      wawwe->lhs.name = var_name;
    if (wawwe->start.name == var)
      wawwe->start.name = var_name;
    if (wawwe->mult.name == var)
      wawwe->mult.name = var_name;
    return wawwe;
  }
  else if (L2::CjumpOperation *cj = dynamic_cast<L2::CjumpOperation *>(i)) {
    if (cj->cexp.lhs.name == var)
      cj->cexp.lhs.name = var_name;
    if (cj->cexp.rhs.name == var)
      cj->cexp.rhs.name = var_name;
    return cj;
  }
  else if (L2::GotoOperation *gt = dynamic_cast<L2::GotoOperation *>(i)) {
    return gt;
  }
}

bool needs_spilled(L2::Instruction *i, string var) {
  if (L2::Load *load = dynamic_cast<L2::Load *>(i))  {
    return (load->lhs.name == var || load->rhs.value.name == var);
  }
  else if (L2::Store *store = dynamic_cast<L2::Store *>(i)) {
    return (store->rhs.name == var || store->lhs.value.name == var);
  }
  else if (L2::Assignment *assn = dynamic_cast<L2::Assignment *>(i)) {
    return (assn->lhs.name == var || assn->rhs.name == var);
  }
  else if (L2::ReturnCall *ret = dynamic_cast<L2::ReturnCall *>(i)) {
    return false;
  }
  else if (L2::ArithmeticOperation *aop = dynamic_cast<L2::ArithmeticOperation *>(i)) {
    return (aop->lhs.name == var || aop->rhs.name == var);
  }
  else if (L2::MemoryArithmeticOperation *maop = dynamic_cast<L2::MemoryArithmeticOperation *>(i)) {
    return (maop->lhs.value.name == var || maop->rhs.name == var);
  }
  else if (L2::MemoryArithmeticOperation2 *maop = dynamic_cast<L2::MemoryArithmeticOperation2 *>(i)) {
    return (maop->lhs.name == var || maop->rhs.value.name == var);
  }
  else if (L2::ShiftOperation *sop = dynamic_cast<L2::ShiftOperation *>(i)) {
    return (sop->lhs.name == var || sop->rhs.name == var);
  }
  else if (L2::ComparisonOperation *comp = dynamic_cast<L2::ComparisonOperation *>(i)) {
    return (comp->lhs.name == var || comp->cexp.lhs.name == var || comp->cexp.rhs.name == var);
  }
  else if (L2::RuntimeCall *rCall = dynamic_cast<L2::RuntimeCall *>(i)) {
    return (rCall->function_name.name == var);
  }
  else if (L2::FunctionCall *fCall = dynamic_cast<L2::FunctionCall *>(i)) {
    return (fCall->function_name.name == var);
  }
  else if (L2::Label *lbl = dynamic_cast<L2::Label *>(i)) {
    return false;
  }
  else if (L2::WawweOperation *wawwe = dynamic_cast<L2::WawweOperation *>(i)) {
    return (wawwe->lhs.name == var || wawwe->start.name == var || wawwe->mult.name == var);
  }
  else if (L2::CjumpOperation *cj = dynamic_cast<L2::CjumpOperation *>(i)) {
    return (cj->cexp.lhs.name == var || cj->cexp.rhs.name == var);
  }
  else if (L2::GotoOperation *gt = dynamic_cast<L2::GotoOperation *>(i)) {
    return false;
  }
  return false;
}

L2::Function *Analysis::spill(L2::Function *f, string var, int n_spilled) {
  string var_name = "_a" + var;
  int stack_index = n_spilled;
  L2::Function *newFn = new L2::Function();
  newFn->name = f->name;
  // when we spill, we now have one more local
  newFn->locals = f->locals + 1;
  newFn->arguments = f->arguments;
  for (auto i : f->instructions) {
    if (needs_spilled(i, var)) {
      var_name = get_var_name(var_name);
      L2::Load *spill_load = generate_spill_load(var_name, stack_index);
      L2::Store *spill_store = generate_spill_store(var_name, stack_index);
      newFn->instructions.push_back(spill_load);
      newFn->instructions.push_back(replace_var(i, var, var_name));
      newFn->instructions.push_back(spill_store);
    } else {
      newFn->instructions.push_back(i);
    }
  }
  delete f;
  return newFn;
}

int64_t get_degree(std::string node) {
  return graph.find(node)->second.size();
}

void remove_node(std::string node) {
  // removes a node from the graph, updating the adjacencies of all others
  // find neighbors
  std::set<std::string>::iterator iter;
  for (auto n : graph) {
    // remove the node from any neighbors of it
    iter = n.second.find(node);
    if (iter != n.second.end()) {
      n.second.erase(iter);
    }
  }
  std::map<string, std::set<string>>::iterator gi = graph.find(node);
  // remove the node itself from the graph
  graph.erase(gi);
}

void insert_node(std::string node) {
  std::set<std::string> interferences = Analysis::adjacencies.find(node)->second;
  std::map<std::string, std::set<std::string>>::iterator gi;
  // iterate over the variables that interfere with this one.
  // look each one up in the current graph, adding this node to its
  // neighbors.
  map<std::string, std::set<std::string>>::iterator node_iter;
  map<std::string, std::set<std::string>>::iterator neighbor_iter;
  node_iter = graph.insert(pair<std::string, std::set<std::string>>(node, std::set<std::string>())).first;
  for (auto n : graph) {
    // iterate through the existing nodes in the graph. if one interferes with node,
    // make sure to each to the other's adjacency
    if (std::find(interferences.begin(), interferences.end(), n.first) != interferences.end()) {
      // they interfere with one another
      neighbor_iter = graph.find(n.first);
      node_iter->second.insert(n.first);
      neighbor_iter->second.insert(node);
    }
  }
}

std::string get_candidate_node(int k = 15) {
  std::string first_pick = "NONE";
  // way to indicate whether it has been found.
  std::string second_pick;
  int first_candidate_degree = -1;
  int second_candidate_degree = -1;
  int c;
  // simultaneously look for the first pick,
  // the node with the highest degree that is less than 15,
  // and the second pick, the node with the highest c.
  for (auto i : graph) {
    if (find(non_spill.begin(), non_spill.end(), i.first) == non_spill.end()) {
      c = get_degree(i.first);
      if (c < k) {
        if (c > first_candidate_degree) {
          first_candidate_degree = c;
          first_pick = i.first;
        }
      }
      if (c > second_candidate_degree) {
        second_candidate_degree = c;
        second_pick = i.first;
      }
    }
  }

  if (first_pick != "NONE") {
    return first_pick;
  }
  return second_pick;
}

void generate_graph(
    vector<set<string>> IN,
    vector<set<string>> OUT,
    vector<set<string>> KILL,
    L2::Function *f) {


  vector<set<string>> LOCAL_IN = IN;
  vector<set<string>> LOCAL_OUT = OUT;

  int c = 0;
  // initial assumptions about intereference with registers
  // are added to the Analysis::adjacencies map
  map<string, set<string>>::iterator adj_iter;
  map<std::string, set<std::string>>::iterator graph_iter;

  for (auto reg1 : x86_registers) {
    Analysis::adjacencies.insert(pair<string, set<string>>(reg1, set<string>()));
    for (auto reg2 : x86_registers) {
      if (reg1 != reg2)
        Analysis::adjacencies.find(reg1)->second.insert(reg2);
    }
  }

  vector<set<string>> lines;
  lines.insert(lines.end(), LOCAL_IN.begin(), LOCAL_IN.end());
  lines.insert(lines.end(), LOCAL_OUT.begin(), LOCAL_OUT.end());
  // KILL and OUT also interfere with eachother!
  for (int line = 0; line < KILL.size(); line++){
    if (!f->instructions[line]->y_to_x_type) {
      set<string> OUT_PLUS_KILL_LINE;
      for (auto v : OUT[line])
        OUT_PLUS_KILL_LINE.insert(v);
      for (auto v : KILL[line])
        OUT_PLUS_KILL_LINE.insert(v);
      lines.push_back(OUT_PLUS_KILL_LINE);
    }
  }

  // iterate over the lines of the liveness output
  // adding all interferences to both the adjacency map
  // and the graph. NOTE: nothing is colored here.
  for (auto line : lines) {
    for (auto i = line.begin(); i != line.end(); ++i) {
      std::string e = *i;
      Analysis::variables.insert(e);
      adj_iter = Analysis::adjacencies.find(e);
      graph_iter = graph.find(e);
      // if this variable isn't yet in the graph, create an empty set of adjacencies
      // to populate. also update its degree
      if (graph_iter == graph.end())
        graph_iter = graph.insert(pair<std::string, set<std::string>>(e, set<std::string>())).first;
      if (adj_iter == Analysis::adjacencies.end())
        adj_iter = Analysis::adjacencies.insert(pair<std::string, set<std::string>>(e, set<std::string>())).first;
      for (auto j = line.begin(); j != line.end(); ++j) {
        if (i != j) {
          std::string v = *j;
          Analysis::variables.insert(v);
          adj_iter->second.insert(v);
          graph_iter->second.insert(v);
        }
      }
    }
  }


  for (auto var: f->variables) {
    // variables that aren't in the liveness analysis aren't interfering with anything but need to be recorded.
    graph_iter = graph.find(var);
    if (graph_iter == graph.end()) {
      Analysis::variables.insert(var);
      Analysis::adjacencies.insert(pair<std::string, set<std::string>>(var, set<std::string>()));
      graph.insert(pair<std::string, set<std::string>>(var, set<std::string>()));
    }
  }
}

bool valid_color(int64_t color, std::string node) {
  map<std::string, std::set<std::string>>::iterator n = graph.find(node);
  // if there are no other elements in the graph, this is by default
  // a valid color for the node
  if (n == graph.end()) {
    return true;
  }

  for (auto neighbor : n->second) {
    if (Analysis::coloring[neighbor] == color) {
      return false;
    }
  }
  return true;
}

int choose_color(std::string node) {
  int c;
  if ((c = std::distance(x86_registers.begin(),
                         std::find(x86_registers.begin(), x86_registers.end(), node))
        ) < x86_registers.size()) {
    return c;
  }
  for (c = 0; c < x86_registers.size(); c++) {
    if (valid_color(c, node)) {
      return c;
    }
  }
  return -1;
}

template <typename T>
T convert_L2_item(T item) {
  auto it = Analysis::coloring.find(item.name);
  if (it != Analysis::coloring.end())
    item.name = x86_registers.at(it->second);
  return item;
}

L2::Function* Analysis::translate_to_L1(L2::Function *f, std::vector<std::string> stack) {
  // returns an L2 function exclusively with L1 instructions
  // first, increase the runtime stack size in order to make room for spilled variables
  // essentially, all spilled instructions will have
  // (non-var-name <- (mem rsp X))
  // (<operaiton on non-var-name>)
  // ((mem rsp X) <- non-var-name)
  int idx;
  for (auto i : f->instructions) {
    if (L2::Load *load = dynamic_cast<L2::Load *>(i)) {
      load->lhs = convert_L2_item(load->lhs);
      load->rhs.value = convert_L2_item(load->rhs.value);
    }
    else if (L2::Store *store = dynamic_cast<L2::Store *>(i)) {
      store->rhs = convert_L2_item(store->rhs);
      store->lhs.value = convert_L2_item(store->lhs.value);
    }
    else if (L2::Assignment *assn = dynamic_cast<L2::Assignment *>(i)) {
      assn->lhs = convert_L2_item(assn->lhs);
      assn->rhs = convert_L2_item(assn->rhs);
    }
    else if (L2::ReturnCall *ret = dynamic_cast<L2::ReturnCall *>(i)) {
      ;
    }
    else if (L2::ArithmeticOperation *aop = dynamic_cast<L2::ArithmeticOperation *>(i)) {
      aop->lhs = convert_L2_item(aop->lhs);
      aop->rhs = convert_L2_item(aop->rhs);
    }
    else if (L2::MemoryArithmeticOperation *maop = dynamic_cast<L2::MemoryArithmeticOperation *>(i)) {
      // rhs is potentially a variable.
      maop->rhs = convert_L2_item(maop->rhs);
    }
    else if (L2::MemoryArithmeticOperation2 *maop = dynamic_cast<L2::MemoryArithmeticOperation2 *>(i)) {
      maop->lhs = convert_L2_item(maop->lhs);
    }
    else if (L2::ShiftOperation *sop = dynamic_cast<L2::ShiftOperation *>(i)) {
      sop->lhs = convert_L2_item(sop->lhs);
      sop->rhs = convert_L2_item(sop->rhs);
    }
    else if (L2::ComparisonOperation *comp = dynamic_cast<L2::ComparisonOperation *>(i)) {
      // comparison is very tedious. lhs, and both halves of the comparison
      // might need to be spilled/have their values replaced with registers
      // to be checked for spilling.
      comp->lhs = convert_L2_item(comp->lhs);
      comp->cexp.lhs = convert_L2_item(comp->cexp.lhs);
      comp->cexp.rhs = convert_L2_item(comp->cexp.rhs);
    }
    else if (L2::RuntimeCall *rCall = dynamic_cast<L2::RuntimeCall *>(i)) {
      rCall->function_name = convert_L2_item(rCall->function_name);
      ;
    }
    else if (L2::FunctionCall *fCall = dynamic_cast<L2::FunctionCall *>(i)) {
      fCall->function_name = convert_L2_item(fCall->function_name);
      ;
    }
    else if (L2::Label *lbl = dynamic_cast<L2::Label *>(i)) {
      ;
    }
    else if (L2::WawweOperation *wawwe = dynamic_cast<L2::WawweOperation *>(i)) {
      wawwe->lhs = convert_L2_item(wawwe->lhs);
      wawwe->start = convert_L2_item(wawwe->lhs);
      wawwe->mult = convert_L2_item(wawwe->mult);
    }
    else if (L2::CjumpOperation *cj = dynamic_cast<L2::CjumpOperation *>(i)) {
      cj->cexp.lhs = convert_L2_item(cj->cexp.lhs);
      cj->cexp.rhs = convert_L2_item(cj->cexp.rhs);
    }
    else if (L2::GotoOperation *gt = dynamic_cast<L2::GotoOperation *>(i)) {
      ;
    } else {
    }
  }

  return f;
}

bool is_number(const std::string& s)
{
  std::string::const_iterator it = s.begin();
  while (it != s.end() && std::isdigit(*it)) ++it;
  return !s.empty() && it == s.end();
}

pair<map<string, int>, vector<string>> Analysis::interference_analysis(
    std::vector<std::set<std::string>> IN,
    std::vector<std::set<std::string>> OUT,
    std::vector<std::set<std::string>> KILL,
    L2::Function *f) {
  Analysis::adjacencies.clear();
  Analysis::variables.clear();
  Analysis::coloring.clear();
  graph.clear();
  // generate the graph containing the nodes and edges representing
  // the interferences.
  // for fast lookup, there is additionally Analysis::adjacencies,
  // mapping a val to its interferences
  generate_graph(IN, OUT, KILL, f);
  // here we have to cheat and find any occurence of a shift and mark its RHS
  // as colored to rcx.

  for (auto i : f->instructions) {
    if (L2::ShiftOperation *sop = dynamic_cast<L2::ShiftOperation *>(i)) {
      if (!(is_number(sop->rhs.name)))
      {
        int rcx_pos = (int) distance(x86_registers.begin(), find(x86_registers.begin(), x86_registers.end(), "rcx"));
        Analysis::coloring[sop->rhs.name] = rcx_pos;
      }
    }
  }
  std::vector<std::string> stack;
  std::string candidate_node = "_";
  while (!graph.empty() && candidate_node.size()) {
    candidate_node = get_candidate_node();
    if (candidate_node.size()) {
      remove_node(candidate_node);
      stack.push_back(candidate_node);
    }
  }
  //add_registers(graph);
  bool valid_coloring = true;
  int color;


  // choose colors for register first
  for (auto reg : x86_registers) {
    insert_node(reg);
    Analysis::coloring[reg] = choose_color(reg);
  }

  while (valid_coloring and !stack.empty()) {
    std::string node = stack.back();
    insert_node(node);
    color = choose_color(node);
    if (color == -1) {
      valid_coloring = false;
    } else {
      stack.pop_back();
      if (Analysis::coloring.find(node) == Analysis::coloring.end())
        Analysis::coloring[node] = color;
    }
  }

  return make_pair(Analysis::coloring, stack);
};
