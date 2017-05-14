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

using namespace std;

map<string, string> register_map;

string wrap_arg(L1::L1_item arg) {
  if (!arg.r) {
    return "$" + arg.name;
  } else {
    return "%" + arg.name;
  }
};

void compile_L1(L1::Program p) {
  register_map.insert(pair<string, string>("r10", "r10b"));
  register_map.insert(pair<string, string>("r11", "r11b"));
  register_map.insert(pair<string, string>("r12", "r12b"));
  register_map.insert(pair<string, string>("r13", "r13b"));
  register_map.insert(pair<string, string>("r14", "r14b"));
  register_map.insert(pair<string, string>("r15", "r15b"));
  register_map.insert(pair<string, string>("r8", "r8b"));
  register_map.insert(pair<string, string>("r9", "r9b"));
  register_map.insert(pair<string, string>("rax", "al"));
  register_map.insert(pair<string, string>("rbp", "bpl"));
  register_map.insert(pair<string, string>("rbx", "bl"));
  register_map.insert(pair<string, string>("rcx", "cl"));
  register_map.insert(pair<string, string>("rdi", "dil"));
  register_map.insert(pair<string, string>("rdx", "dl"));
  register_map.insert(pair<string, string>("rsi", "sil"));

  ofstream outputFile;
  outputFile.open("prog.S");
  outputFile << "\t.text\n\t.globl go\ngo:\n\tpushq %rbx\n\tpushq %rbp\n\tpushq %r12\n\tpushq %r13\n\tpushq %r14\n\tpushq %r15\n\n\tcall ";
  outputFile << p.entryPointLabel.replace(0,1,"_") << "\n" << endl;
  outputFile << "\n\tpopq %r15\n\tpopq %r14\n\tpopq %r13\n\tpopq %r12\n\tpopq %rbp\n\tpopq %rbx\n\n\tretq\n";

  /* Generate x86_64 code
   */
  for (auto f : p.functions){
    outputFile << f->name.replace(0,1,"_") << ":\n";
    outputFile << "\tsubq $" << f->locals * 8 << ", %rsp\n";
    for (L1::Instruction* i : f->instructions){
      if (L1::Load *load = dynamic_cast<L1::Load *>(i)) {
        outputFile << "\tmovq " << load->rhs.offset_int << "(" << wrap_arg(load->rhs.value) << "), " << wrap_arg(load->lhs) << endl;
      }
      else if (L1::Store *store = dynamic_cast<L1::Store *>(i)) {
        outputFile << "\tmovq " << wrap_arg(store->rhs) << ", " << store->lhs.offset_int << "(" << wrap_arg(store->lhs.value) << ")\n";
      } 
      else if (L1::Assignment *assn = dynamic_cast<L1::Assignment *>(i)) {
        outputFile << "\tmovq " << wrap_arg(assn->rhs) << ", " << wrap_arg(assn->lhs) << "\n";
      } 
      else if (L1::ReturnCall *ret = dynamic_cast<L1::ReturnCall *>(i)) {
        int n_stack_args = 0;
        if (f->arguments > 6) {
          n_stack_args = f->arguments - 6;
        }
        outputFile << "\taddq $" << f->locals * 8 + n_stack_args * 8 << ", %rsp\n";
        outputFile << "\tretq\n";
      }
      else if (L1::ArithmeticOperation *aop = dynamic_cast<L1::ArithmeticOperation *>(i)) {
        std::string aop_string;
        switch(aop->op) {
          case L1::plusequal:
            aop_string = "addq ";
            break;
          case L1::minusequal:
            aop_string = "subq ";
            break;
          case L1::timesequal:
            aop_string = "imulq ";
            break;
          case L1::andequal:
            aop_string = "andq ";
            break;
          default:
            break;
        }
        outputFile << "\t" << aop_string << wrap_arg(aop->rhs) << ", " << wrap_arg(aop->lhs) << endl;
      } 
      else if (L1::MemoryArithmeticOperation *maop = dynamic_cast<L1::MemoryArithmeticOperation *>(i)) {
        std::string maop_string;
        switch(maop->op) {
          case L1::plusequal:
            maop_string = "addq ";
            break;
          case L1::minusequal:
            maop_string = "subq ";
            break;
          default:
            break;
        }
        outputFile << "\t" << maop_string <<  wrap_arg(maop->rhs) << ", " << maop->lhs.offset_int << "(%" << maop->lhs.value.name << ")\n";
      }
      else if (L1::MemoryArithmeticOperation2 *maop = dynamic_cast<L1::MemoryArithmeticOperation2 *>(i)) {
        std::string maop_string;
        switch(maop->op) {
          case L1::plusequal:
            maop_string = "addq ";
            break;
          case L1::minusequal:
            maop_string = "subq ";
            break;
          default:
            break;
        }
        outputFile << "\t" << maop_string << maop->rhs.offset_int << "(%" << maop->rhs.value.name << "), " << wrap_arg(maop->lhs) << endl;
      }
      else if (L1::ShiftOperation *sop = dynamic_cast<L1::ShiftOperation *>(i)) {
        std::string sop_string;
        switch(sop->op) {
          case L1::lshift:
            sop_string = "salq ";
            break;
          case L1::rshift:
            sop_string = "sarq ";
            break;
          default:
            break;
        }
        outputFile << "\t" << sop_string << sop->rhs.name << ", " << wrap_arg(sop->lhs) << endl;
      } 
      else if (L1::ComparisonOperation *comp = dynamic_cast<L1::ComparisonOperation *>(i)) {
        std::string lhs;
        std::string c_lhs;
        std::string c_rhs;
        std::string cop;
        std::string eightbitreg;
        bool reverse = false;

        if (!comp->cexp.lhs.r && !comp->cexp.rhs.r) {
          // both are numbers. evaluate at compile time.
          int lhs_int = std::stoi(comp->cexp.lhs.name);
          int rhs_int = std::stoi(comp->cexp.rhs.name);
          bool result;
          switch(comp->cexp.op) {
            case L1::lessthan:
              result = lhs_int < rhs_int;
              break;
            case L1::lessthanorequal:
              result = lhs_int <= rhs_int;
              break;
            case L1::equal:
              result = lhs_int == rhs_int;
              break;
            default: break;
          }
          outputFile << "\tmovq $" << result << ", " << wrap_arg(comp->lhs) << endl;
        } else {

          if (!comp->cexp.lhs.r) {
            // comparison with a constant
            reverse = true;
          }
          if (reverse) {
            c_lhs = wrap_arg(comp->cexp.lhs);
            c_rhs = wrap_arg(comp->cexp.rhs);
          } else {
            c_lhs = wrap_arg(comp->cexp.rhs);
            c_rhs = wrap_arg(comp->cexp.lhs);
          }

          if (reverse) {
            switch(comp->cexp.op) {
              case L1::lessthan:
                cop = "setg ";
                break;
              case L1::lessthanorequal:
                cop = "setge ";
                break;
              case L1::equal:
                cop = "sete ";
                break;
              default:
                break;
            }
          } else {
            switch(comp->cexp.op) {
              case L1::lessthan:
                cop = "setl ";
                break;
              case L1::lessthanorequal:
                cop = "setle ";
                break;
              case L1::equal:
                cop = "sete ";
                break;
              default: break;
            }
          }

          eightbitreg = register_map.find(comp->lhs.name)->second;

          outputFile << "\tcmpq " << c_lhs << ", " << c_rhs << "\n\t" << cop << "%" << eightbitreg << "\n\tmovzbq %" << eightbitreg << ", %" << comp->lhs.name << endl;
        }
      }
      else if (L1::FunctionCall *fCall = dynamic_cast<L1::FunctionCall *>(i)) {
        std::string f_name = fCall->function_name.name;
        for(std::map<std::string,std::string>::iterator iter = register_map.begin(); iter != register_map.end(); ++iter)
        {
          std::string k = iter->first;
          if (k == f_name) {
            f_name = "*%" + f_name;
            break;
          }
        }
        int n_stack_args = 0;
        if (fCall->n_args > 6) {
          n_stack_args = fCall->n_args - 6;
        }
        outputFile << "\tsubq $" << n_stack_args * 8 + 8 << ", %rsp\n\tjmp " << f_name << endl;
      }
      else if (L1::RuntimeCall *rCall = dynamic_cast<L1::RuntimeCall *>(i)) {
        outputFile << "\tcall " << rCall->function_name.name << endl;
      }
      else if (L1::Label *lbl = dynamic_cast<L1::Label *>(i)) {
        outputFile << lbl->name << ":\n";
      }
      else if (L1::WawweOperation *wawwe = dynamic_cast<L1::WawweOperation *>(i)) {
        outputFile << "\tlea (%" << wawwe->start.name << ", %" << wawwe->mult.name << ", " << wawwe->e << "), %" << wawwe->lhs.name << endl;
      }
      else if (L1::CjumpOperation *cj = dynamic_cast<L1::CjumpOperation *>(i)) {
        bool reverse = !cj->cexp.lhs.r;
        std::string jmp_string;
        std::string cmp_lhs;
        std::string cmp_rhs;

        if (!cj->cexp.lhs.r && !cj->cexp.rhs.r) {
          // number to number comparison
          int lhs_int = std::stoi(cj->cexp.lhs.name);
          int rhs_int = std::stoi(cj->cexp.lhs.name);
          bool correct = false;
          switch(cj->cexp.op) {
            case L1::lessthan:
              correct = lhs_int < rhs_int;
              break;
            case L1::lessthanorequal:
              correct = lhs_int <= rhs_int;
              break;
            case L1::equal:
              correct = lhs_int == rhs_int;
              break;
            default: break;
          }
          if (correct) {
            outputFile << "\tjmp " << cj->then_label << endl;
          } else {
            outputFile << "\tjmp " << cj->else_label << endl;
          }
        } else {
        
          if (reverse) {
            cmp_lhs = wrap_arg(cj->cexp.lhs);
            cmp_rhs = wrap_arg(cj->cexp.rhs);
          } else {
            cmp_lhs = wrap_arg(cj->cexp.rhs);
            cmp_rhs = wrap_arg(cj->cexp.lhs);
          }

          if (reverse) {
            switch(cj->cexp.op) {
              case L1::lessthan:
                jmp_string = "jg ";
                break;
              case L1::lessthanorequal:
                jmp_string = "jge ";
                break;
              case L1::equal:
                jmp_string = "je ";
                break;
              default: break;
            }
          } else {
            switch(cj->cexp.op) {
              case L1::lessthan:
                jmp_string = "jl ";
                break;
              case L1::lessthanorequal:
                jmp_string = "jle ";
                break;
              case L1::equal:
                jmp_string = "je ";
                break;
              default: break;
            }
          }
          outputFile << "\tcmpq " << cmp_lhs << ", " << cmp_rhs << "\n\t" << jmp_string << " " << cj->then_label << "\n\tjmp " << cj->else_label << endl;
        }
      }
      else if (L1::GotoOperation *gt = dynamic_cast<L1::GotoOperation *>(i)) {
        outputFile << "\tjmp " << gt->lbl.name << endl;
        outputFile << "\tjmp " << gt->lbl.name << endl;
      }
    }
  }

  outputFile.close();

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

  /* Parse the L1 program.
   */
  L1::Program p = L1::L1_parse_file(argv[optind]);
  compile_L1(p);

  return 0;
}
