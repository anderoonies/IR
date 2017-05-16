#include <vector>
#include <iostream>
#include <fstream>

#include "compiler.h"

using namespace std;

int encode(int n) {
  return (n << 1) + 1;
};

int decode(int n) {
  return (n >> 1) - 1;
};

string get_free_var(string seed, shared_ptr<IR::Function> f) {
  string var = seed;
  bool valid;
  do {
    valid = true;
    for (auto bb : f->blocks)
      for (auto i : bb->instructions) {
        if (i->contains(var))
          valid = false;
      }
    if (!valid)
      var = "o" + var;
  } while (!valid);
  return var;
};

vector<string> get_free_vars(string seed, int n_vars, shared_ptr<IR::Function> f) {
  vector<string> vars;
  for (int i = 0; i < n_vars; i++) {
    string v_seed = seed + to_string(i);
    vars.push_back(get_free_var(v_seed, f));
  }
  return vars;
};

string write_offset(ofstream &output, shared_ptr<IR::Function> f, shared_ptr<IR::Instruction> i) {
  vector<IR::IR_t> dimensions;
  string arr;
  vector<IR::IR_t> indices;
  shared_ptr<IR::ArrayAllocate> alloc;
  dimensions = alloc->dimensions;
  if (shared_ptr<IR::IndexWrite> write = dynamic_pointer_cast<IR::IndexWrite>(i)) {
    alloc = dynamic_pointer_cast<IR::ArrayAllocate>(f->data_structs.find(write->lhs.name)->second);
    arr = write->lhs.name; 
    indices = write->indices;
  } else if (shared_ptr<IR::IndexRead> read = dynamic_pointer_cast<IR::IndexRead>(i)) {
    alloc = dynamic_pointer_cast<IR::ArrayAllocate>(f->data_structs.find(read->rhs.name)->second);
    arr = read->rhs.name;
    indices = read->indices;
  }
  // dim_vars are L, M, N, etc.
  vector<string> dim_vars = get_free_vars("dim", dimensions.size(), f);
  // addr_vars are ADDR_M, etc.
  vector<string> addr_vars = get_free_vars("addr", dimensions.size(), f);
  // newvars are newVar1, newVar2. etc. not clear if they're needed yet
  vector<string> newvars = get_free_vars("newVar", dimensions.size(), f);
  // indexvars may not be needed.
  vector<string> indexvars = get_free_vars("idx", dimensions.size(), f);
  // mult is where the factor to multiply the offset by is stored
  string mult = get_free_var("mult", f);
  // index is 'index'
  string index = get_free_var("index", f);
  // offset
  string offset = get_free_var("offset", f);
  // addr
  string addr = get_free_var("addr", f);

  for (int i = dimensions.size() - 1; i >= 0; i--) {
    output << addr_vars.at(i) << " <- " << arr << " + " << (16 + i * 8) << endl;
    output << dim_vars.at(i) << " <- load " << addr_vars.at(i) << endl;
    output << dim_vars.at(i) << " <- " << dim_vars.at(i) << " >> 1\n";
  }
  output << mult << " <- " << dimensions.back().name << endl;
  for (int i = dimensions.size() - 1; i > 0; i--) {
    output << indexvars.at(i) << " <- " << indices.at(i).name << endl;
    output << index << " <- " << indexvars.at(i) << " * " << mult << endl;
    output << mult << " <- " << mult << " * " << dimensions.at(i - 1).name << endl;
  }
  output << index << " <- " << index << " + " << indices.back().name << endl;
  output << offset << " <- " << index << " * 8\n";
  output << offset << " <- " << index << " + " << (16 + (8 * dimensions.size())) << endl;
  output << addr << " <- " << arr << " + " << offset << endl;
  return addr;
};

void Compiler::Compile(IR::Program p) {
  ofstream output;
  output.open("prog.L3");

  for (auto f : p.functions) {
    // write the function name and its args
    output << "define " << f->name << "( ";
    for (auto dec : f->vars)
      output << dec.type.toString() << " " << dec.var.name << ", ";
    output << "){\n";
    for (auto bb : f->blocks) {
      output << bb->entry_point.name << endl;
      for (auto i : bb->instructions) {
        // write the instructions one by one!
        if (shared_ptr<IR::Assignment> assn = dynamic_pointer_cast<IR::Assignment>(i)) 
        {
          output << assn->lhs.name << " <- " << assn->rhs.name << endl;
        }
        else if (shared_ptr<IR::Operation> op = dynamic_pointer_cast<IR::Operation>(i))
        {
          string op_string;
          switch(op->op) {
            case IR::plus:
              op_string = "+";
              break;
            case IR::minus:
              op_string = "-";
              break;
            case IR::times:
              op_string = "*";
              break;
            case IR::l3and:
              op_string = "&";
              break;
            case IR::lshift:
              op_string = "<<";
              break;
            case IR::rshift:
              op_string = ">>";
              break;
            case IR::lt:
              op_string = "<";
              break;
            case IR::lte:
              op_string = "<=";
              break;
            case IR::eq:
              op_string = "=";
              break;
            case IR::gt:
              op_string = ">";
              break;
            case IR::gte:
              op_string = ">=";
              break;
            default:
              break;
          }
          output << op->lhs.name << " <- " << op->op_lhs.name << " " << op_string << " " << op->op_rhs.name << endl;
        }
        else if (shared_ptr<IR::Return> ret = dynamic_pointer_cast<IR::Return>(i))
        {
          output << "return" << endl;
        }
        else if (shared_ptr<IR::ReturnValue> retv = dynamic_pointer_cast<IR::ReturnValue>(i))
        {
          output << "return " << retv->value.name << endl;
        }
        else if (shared_ptr<IR::Label> label = dynamic_pointer_cast<IR::Label>(i))
        {
          output << label->label.name << endl;
        }
        else if (shared_ptr<IR::Branch> branch = dynamic_pointer_cast<IR::Branch>(i))
        {
          output << "br " << branch->dest.name << endl;
        }
        else if (shared_ptr<IR::CBranch> cbranch = dynamic_pointer_cast<IR::CBranch>(i))
        {
          output << "br " << cbranch->condition.name << " " << cbranch->then_dest.name << " " << cbranch->else_dest.name << endl;
        }
        else if (shared_ptr<IR::Call> call = dynamic_pointer_cast<IR::Call>(i))
        {
          if (call->callee.name[0] == '%')
            call->callee.name.erase(0,1);
          output << "call " << call->callee.name << "(";
          if (call->args.size() > 1)
            for (auto arg : call->args)
              output << arg.name << ", ";
          else if (call->args.size() == 1)
            output << call->args.at(0).name;
          output << ")\n";
        }
        else if (shared_ptr<IR::TupleAllocate> alloc = dynamic_pointer_cast<IR::TupleAllocate>(i))
        {
          output << alloc->lhs.name << " <- call allocate(" << alloc->dimension.name << ", 1)\n";
        }
        else if (shared_ptr<IR::ArrayAllocate> alloc = dynamic_pointer_cast<IR::ArrayAllocate>(i))
        {
          string v0 = get_free_var("v0", f);
          vector<string> dim_vars = get_free_vars("dim", alloc->dimensions.size(), f);
          // iterate over the freevars, for each one:
          // freevar <- dim >> 1
          int dim = 0;
          for (auto dim_var : dim_vars) {
            output << dim_var << " <- " << alloc->dimensions.at(dim).name << " >> 1\n";
            dim++;
          }
          // then, v0 <- freevar1 * freevar2
          if (alloc->dimensions.size() == 1)
            output << v0 << " <- " << dim_vars.at(0) << endl;
          else {
            output << v0 << " <- " << dim_vars.at(0) << endl;
            for (int i = 1; i < dim_vars.size(); i++)
              output << v0 << " <- " << v0 << " * " << dim_vars[i] << endl;
          }
          // v0 <- v0 << 1
          output << v0 << " <- " << v0 << " << 1\n";
          // v0 <- v0 +1
          output << v0 << " <- " << v0 << " + 1\n";
          // v0 <- v0 + \encode(dim.size() + 1)
          output << v0 << " <- " << v0 << " + " << encode(alloc->dimensions.size()) << endl;
          // v0 <- call allocate(v0, 1)
          output << alloc->lhs.name << " <- call allocate(" << v0 << ", 1)\n";
          // vo <- v0 + 8
          output << v0 << " <- " << alloc->lhs.name << " + 8\n";
          // store v0 <- \encode(dim.size())
          output << "store " << v0 << " <- " << encode(alloc->dimensions.size()) << endl;
          // for each dim:
          // v0 <- v0 + 8
          // store v0 <- dim
          for (int i = 0; i < alloc->dimensions.size(); i++) {
            output << v0 << " <- " << alloc->lhs.name << " + " << (1 + i + alloc->dimensions.size()) * 8 << endl;
            output << "store " << v0 << " <- " << alloc->dimensions[i].name << endl;
          }
        }
        else if (shared_ptr<IR::IndexWrite> write = dynamic_pointer_cast<IR::IndexWrite>(i))
        {
          shared_ptr<IR::Instruction> alloc = f->data_structs.find(write->lhs.name)->second;
          if (shared_ptr<IR::ArrayAllocate> array_alloc = dynamic_pointer_cast<IR::ArrayAllocate>(alloc)) {
            string addr = write_offset(output, f, write);
            output << "store " << addr << " <- " << write->rhs.name << endl;
          } else {
            cout << "doing tuple\n";
            string newVar = get_free_var("newVar", f);
            output << newVar << " <- " << write->lhs.name << " + 8\n";
            output << "store " << newVar << " <- " << write->rhs.name << endl;
          }
        }
        else if (shared_ptr<IR::IndexRead> read = dynamic_pointer_cast<IR::IndexRead>(i))
        {
          string addr = write_offset(output, f, read);
          shared_ptr<IR::Instruction> alloc = f->data_structs.find(write->lhs.name)->second;
          if (shared_ptr<IR::ArrayAllocate> array_alloc = dynamic_pointer_cast<IR::ArrayAllocate>(alloc)) {
            string addr = write_offset(output, f, write);
            output << read->rhs.name << " <- load " << addr << endl;
          } else {
            cout << "doing tuple\n";
            string newVar = get_free_var("newVar", f);
            output << newVar << " <- " << read->rhs.name << " + 8\n";
            output << read->lhs.name << " <- load " << newVar << endl;
          }
        }
        else if (shared_ptr<IR::LengthRead> lr = dynamic_pointer_cast<IR::LengthRead>(i))
        {
          string v0 = get_free_var("v0", f);
          string v1 = get_free_var("v1", f);
          string v2 = get_free_var("v2", f);
          output << v0 << " <- " << lr->index.name << " * 8\n";
          output << v1 << " <- " << v0 << " + 16\n";
          output << v2 << " <- " << lr->rhs.name << " + " << v1 << endl;
          output << lr->lhs.name << " <- load " << v2 << endl;
        }
      }
    }
    output << "}\n";
  }
  output << "}\n";
  return;
};
