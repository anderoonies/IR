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

#include "parser.h"
#include "interference.h"

using namespace std;

std::vector<std::string> caller_save_registers = {
  "r10", "r11", "r8", "r9", "rax", "rcx", "rdi", "rdx", "rsi"
};

std::vector<std::string> callee_save_registers = {
  "r12", "r13", "r14", "r15", "rbp", "rbx"
};

std::vector<std::string> arg_registers = {
  "rdi", "rsi", "rdx", "rcx", "r8", "r9"
};

void dump_program(L2::Program p) {
  ofstream outputFile;
  outputFile.open("prog.L1");
  outputFile << "(" << p.entryPointLabel << endl;
  for (auto f : p.functions) {
    outputFile << "(" << f->name << "\n" << f->arguments << " " << f->locals << endl;
    for (auto i : f->instructions) {
      if (L2::Load *load = dynamic_cast<L2::Load *>(i)) {
        outputFile << "(" << load->lhs.name << " <- (mem " << load->rhs.value.name << " " << load->rhs.offset_int << "))\n";
      }
      else if (L2::Store *store = dynamic_cast<L2::Store *>(i)) {
        outputFile << "((mem " << store->lhs.value.name<< " " << store->lhs.offset_int << ") <- " << store->rhs.name << ")\n";
      }
      else if (L2::Assignment *assn = dynamic_cast<L2::Assignment *>(i)) {
        outputFile << "(" << assn->lhs.name << " <- " << assn->rhs.name << ")\n";
      }
      else if (L2::ReturnCall *ret = dynamic_cast<L2::ReturnCall *>(i)) {
        outputFile << "(return)\n";
      }
      else if (L2::ArithmeticOperation *aop = dynamic_cast<L2::ArithmeticOperation *>(i)) {
        string aop_string;
        switch(aop->op) {
          case L2::plusequal:
            aop_string = "+=";
            break;
          case L2::minusequal:
            aop_string = "-=";
            break;
          case L2::andequal:
            aop_string = "&=";
            break;
          case L2::timesequal:
            aop_string = "*=";
            break;
        }
        outputFile << "(" << aop->lhs.name << " " << aop_string << " " << aop->rhs.name << ")\n";
      }
      else if (L2::MemoryArithmeticOperation *maop = dynamic_cast<L2::MemoryArithmeticOperation *>(i)) {
        string maop_string;
        switch(maop->op) {
          case L2::plusequal:
            maop_string = "+=";
            break;
          case L2::minusequal:
            maop_string = "-=";
            break;
          case L2::andequal:
            maop_string = "&=";
            break;
          case L2::timesequal:
            maop_string = "*=";
            break;
        }
        outputFile << "((mem " << maop->lhs.value.name << " " << maop->lhs.offset_int << ") " <<  maop_string << " " << maop->rhs.name << ")\n";
      }
      else if (L2::MemoryArithmeticOperation2 *maop = dynamic_cast<L2::MemoryArithmeticOperation2 *>(i)) {
        string maop_string;
        switch(maop->op) {
          case L2::plusequal:
            maop_string = "+=";
            break;
          case L2::minusequal:
            maop_string = "-=";
            break;
          case L2::andequal:
            maop_string = "&=";
            break;
          case L2::timesequal:
            maop_string = "*=";
            break;
        }
        outputFile << "(" << maop->lhs.name << " " << maop_string << " (mem " << maop->rhs.value.name << " " << maop->rhs.offset_int << "))\n";
      }
      else if (L2::ShiftOperation *sop = dynamic_cast<L2::ShiftOperation *>(i)) {
        string sop_string;
        switch(sop->op) {
          case L2::lshift:
            sop_string = "<<=";
            break;
          case L2::rshift:
            sop_string = ">>=";
            break;
        }
        outputFile << "(" << sop->lhs.name << " " << sop_string << " " << sop->rhs.name << ")\n";
      }
      else if (L2::ComparisonOperation *comp = dynamic_cast<L2::ComparisonOperation *>(i)) {
        string cexp_op_string;
        switch(comp->cexp.op) {
          case L2::lessthan:
            cexp_op_string = "<";
            break;
          case L2::lessthanorequal:
            cexp_op_string = "<=";
            break;
          case L2::equal:
            cexp_op_string = "=";
            break;
        }
        outputFile << "(" << comp->lhs.name << " <- " << comp->cexp.lhs.name << " " << cexp_op_string << " " << comp->cexp.rhs.name << ")\n";
      }
      else if (L2::RuntimeCall *rCall = dynamic_cast<L2::RuntimeCall *>(i)) {
        outputFile << "(call " << rCall->function_name.name << " " << rCall->n_args << ")\n";
      }
      else if (L2::FunctionCall *fCall = dynamic_cast<L2::FunctionCall *>(i)) {
        outputFile << "(call " << fCall->function_name.name << " " << fCall->n_args << ")\n";
      }
      else if (L2::Label *lbl = dynamic_cast<L2::Label *>(i)) {
        outputFile << lbl->name << endl;
      }
      else if (L2::WawweOperation *wawwe = dynamic_cast<L2::WawweOperation *>(i)) {
        outputFile << "(" << wawwe->lhs.name << " @ " << wawwe->start.name << " " << wawwe->mult.name << " " << wawwe->e << ")\n";
      }
      else if (L2::CjumpOperation *cj = dynamic_cast<L2::CjumpOperation *>(i)) {
        string cexp_op_string;
        switch(cj->cexp.op) {
          case L2::lessthan:
            cexp_op_string = "<";
            break;
          case L2::lessthanorequal:
            cexp_op_string = "<=";
            break;
          case L2::equal:
            cexp_op_string = "=";
            break;
        }
        outputFile << "(cjump " << cj->cexp.lhs.name << " " << cexp_op_string << " " << cj->cexp.rhs.name << " " << cj->then_label << " " << cj->else_label << ")\n";
      }
      else if (L2::GotoOperation *gt = dynamic_cast<L2::GotoOperation *>(i)) {
        outputFile << "(goto " << gt->lbl.name << ")\n";
      }

    }
    outputFile << ")\n";
  }
  outputFile << ")\n";
  outputFile.close();
}

template <typename T>
std::set<T> custom_set_union(const std::set<T>& a, const std::set<T>& b)
{
  std::set<T> result = a;
  result.insert(b.begin(), b.end());
  return result;
}

pair<vector<set<string>>, vector<set<string>>>
     generate_in_out(std::vector<std::set<std::string>> GEN,
                     std::vector<std::set<std::string>> KILL,
                     std::vector<std::set<std::string>> IN,
                     std::vector<std::set<std::string>> OUT,
                     std::vector<std::vector<int>> successors){
  if (GEN.size() != KILL.size()) {
    cerr << "SIZE MISMATCH!!" << endl;
  }


  // initialize
  for (int i = 0; i < GEN.size(); i++) {
    IN.push_back(std::set<std::string>());
    OUT.push_back(std::set<std::string>());
  }

  bool change = true;
  do {
    change = false;
    for (int i = GEN.size() - 1; i >= 0; --i) {
      std::set<std::string> OLD_OUT = OUT.at(i);
      std::set<std::string> OLD_IN = IN.at(i);
      if (i < successors.size() - 1) {
        for (auto s_i : successors[i]) {
          for (auto in_value : IN.at(s_i)) {
            OUT.at(i).insert(in_value);
          }
        }
      }
      std::set<std::string> OUT_KILL;
      std::set_difference(
          OUT.at(i).begin(), OUT.at(i).end(), KILL.at(i).begin(), KILL.at(i).end(),
          std::inserter(OUT_KILL, OUT_KILL.end()));
      IN.at(i) = custom_set_union(GEN.at(i), OUT_KILL);
      if ((OLD_OUT != OUT.at(i)) || (OLD_IN != IN.at(i))) {
        change = true;
      }
    }
  } while( change );

  // print
  //cout << "(\n(in\n";
  //for (auto line : IN) {
  //  cout << "(";
  //  for (auto val : line) {
  //    cout << val << " ";
  //  }
  //  cout << ")\n";
  //}
  //cout << ")\n\n";
  //cout << "(out" << endl;
  //for (auto line : OUT) {
  //  cout << "(";
  //  for (auto val : line) {
  //    cout << val << " ";
  //  }
  //  cout << ")\n";
  //}
  //cout << ")\n\n)\n";
  return pair<vector<set<string>>, vector<set<std::string>>>(IN, OUT);
};

L2::Liveness liveness_analysis(L2::Function *f) {
  std::vector<std::set<std::string>> GEN;
  std::vector<std::set<std::string>> KILL;
  std::vector<std::set<std::string>> IN;
  std::vector<std::set<std::string>> OUT;
  std::vector<std::vector<int>> successors;

  int int_i = 0;
  for (auto i : f->instructions) {
    GEN.push_back(std::set<std::string>());
    KILL.push_back(std::set<std::string>());
    successors.push_back({});
    if (L2::Load *load = dynamic_cast<L2::Load *>(i)) {
      KILL.back().insert(load->lhs.name);
      if (load->rhs.value.name != "rsp")
        GEN.back().insert(load->rhs.value.name);
    }
    else if (L2::Store *store = dynamic_cast<L2::Store *>(i)) {
      if (store->rhs.r)
        GEN.back().insert(store->rhs.name);
      if (store->lhs.value.name != "rsp")
        GEN.back().insert(store->lhs.value.name);
    }
    else if (L2::Assignment *assn = dynamic_cast<L2::Assignment *>(i)) {
      if (assn->rhs.r)
        GEN.back().insert(assn->rhs.name);
      KILL.back().insert(assn->lhs.name);
    }
    else if (L2::ReturnCall *ret = dynamic_cast<L2::ReturnCall *>(i)) {
      GEN.back().insert("rax");
      for (auto r : callee_save_registers) {
        GEN.back().insert(r);
      }
    }
    else if (L2::ArithmeticOperation *aop = dynamic_cast<L2::ArithmeticOperation *>(i)) {
      if (aop->rhs.r) {
        GEN.back().insert(aop->rhs.name);
      }
      GEN.back().insert(aop->lhs.name);
      KILL.back().insert(aop->lhs.name);
    }
    else if (L2::MemoryArithmeticOperation *maop = dynamic_cast<L2::MemoryArithmeticOperation *>(i)) {
      if (maop->lhs.value.r)
        GEN.back().insert(maop->lhs.value.name);
      if (maop->rhs.r)
        GEN.back().insert(maop->rhs.name);
    }
    else if (L2::MemoryArithmeticOperation2 *maop = dynamic_cast<L2::MemoryArithmeticOperation2 *>(i)) {
      if (maop->lhs.r)
        GEN.back().insert(maop->lhs.name);
      if (maop->rhs.value.r)
        GEN.back().insert(maop->rhs.value.name);
    }
    else if (L2::ShiftOperation *sop = dynamic_cast<L2::ShiftOperation *>(i)) {
      if (sop->lhs.r)
        KILL.back().insert(sop->lhs.name);
      if (sop->rhs.r)
        GEN.back().insert(sop->rhs.name);
    }
    else if (L2::ComparisonOperation *comp = dynamic_cast<L2::ComparisonOperation *>(i)) {
      KILL.back().insert(comp->lhs.name);
      if (comp->cexp.lhs.r)
        GEN.back().insert(comp->cexp.lhs.name);
      if (comp->cexp.rhs.r)
        GEN.back().insert(comp->cexp.rhs.name);
    }
    else if (L2::RuntimeCall *rCall = dynamic_cast<L2::RuntimeCall *>(i)) {
      KILL.back().insert("rax");
      for (auto c_r : caller_save_registers) {
        KILL.back().insert(c_r);
      }
      for (auto arg : arg_registers) {
        GEN.back().insert(arg);
      }
    }
    else if (L2::FunctionCall *fCall = dynamic_cast<L2::FunctionCall *>(i)) {
      KILL.back().insert("rax");
      for (auto c_r : caller_save_registers) {
        KILL.back().insert(c_r);
      }
      // if it's a non-label function call, it's var or register
      if (!(fCall->function_name.name[0] == ':' ||
            fCall->function_name.name == "print" ||
            fCall->function_name.name == "allocate" ||
            fCall->function_name.name == "array-error"))
      {
        GEN.back().insert(fCall->function_name.name);
      }
      std::vector<std::string> relevant_arg_registers;
      relevant_arg_registers = std::vector<std::string>(arg_registers.begin(), arg_registers.begin() + std::min((int)fCall->n_args, 6));
      for (auto arg : relevant_arg_registers) {
        GEN.back().insert(arg);
      }
    }
    else if (L2::Label *lbl = dynamic_cast<L2::Label *>(i)) {

    }
    else if (L2::WawweOperation *wawwe = dynamic_cast<L2::WawweOperation *>(i)) {
      KILL.back().insert(wawwe->lhs.name);
      GEN.back().insert(wawwe->start.name);
      GEN.back().insert(wawwe->mult.name);
    }
    else if (L2::CjumpOperation *cj = dynamic_cast<L2::CjumpOperation *>(i)) {
      // look for the successors
      for (int j = int_i; j != f->instructions.size(); j++) {
        if (L2::Label *lbl = dynamic_cast<L2::Label *>(f->instructions[j])) {
          if (lbl->name == cj->else_label || lbl->name == cj->then_label) {
            successors.back().push_back(j);
          }
        }
      }
      if (cj->cexp.lhs.r)
        GEN.back().insert(cj->cexp.lhs.name);
      if (cj->cexp.rhs.r)
        GEN.back().insert(cj->cexp.rhs.name);
    }
    else if (L2::GotoOperation *gt = dynamic_cast<L2::GotoOperation *>(i)) {
      for (int j = int_i; j != f->instructions.size(); ++j) {
        if (L2::Label *lbl = dynamic_cast<L2::Label *>(f->instructions[j])) {
          if (lbl->name == gt->lbl.name) {
            successors.back().push_back(j);
          }
        }
      }
    }
    if (!successors.back().size())
      successors.back().push_back({int_i + 1});

    ++int_i;
  }
  pair<vector<set<std::string>>, vector<set<std::string>>> IN_OUT = generate_in_out(GEN, KILL, IN, OUT, successors);
  L2::Liveness liveness;
  liveness.GEN = GEN;
  liveness.KILL = KILL;
  liveness.IN = IN_OUT.first;
  liveness.OUT = IN_OUT.second;
  liveness.successors = successors;

  return liveness;
}

int main(
  int argc,
  char **argv
  ){
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

  /* Parse the L2 program.
   */
  L2::Program p = L2::L2_parse_file(argv[optind]);

  /* Generate GEN/KILL first
   */
  L2::Program *newP = new L2::Program();
  newP->entryPointLabel = p.entryPointLabel;
  int int_i;
  for (auto f : p.functions) {
    bool spilled = false;
    bool needs_spilled = false;
    int n_spilled = 0;
    int doof;
    pair<map<string, int>, vector<string>> analysis;
    do {
      spilled = false;
      L2::Liveness liveness = liveness_analysis(f);
      analysis = Analysis::interference_analysis(liveness.IN, liveness.OUT, liveness.KILL, f);
      needs_spilled = analysis.second.size() > 0;
      if (needs_spilled) {
        for (auto v : analysis.second) {
          spilled = true;
          f = Analysis::spill(f, v, f->locals+1);
        }
      }
    } while (spilled == true);
    f = Analysis::translate_to_L1(f, analysis.second);
    newP->functions.push_back(f);
  }

  dump_program(*newP);
  return 0;
}
