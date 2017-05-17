#pragma once

#include <vector>
#include <string>
#include <memory>
#include <map>

using namespace std;

namespace IR {
  extern vector<string> caller_save_registers;
  extern vector<string> callee_save_registers;
  extern vector<string> arg_registers;

  struct IR_item {
    string name;
    bool operator==(const IR_item &other) const {
      return name == other.name;
    }
  };

  struct Variable : public IR_item {};

  struct IR_s : IR_item {};

  struct IR_t : IR_item {};

  struct IR_u : IR_item {};

  struct IR_callee : IR_item {
    bool runtime = false;
  };

  enum type { array, tuple, integer, code };

  struct Type { 
    type dec_type;
    int array_dim = 0;
  };

  enum Operator { plus, minus, times, l3and, lshift, rshift,
                    lt, lte, eq, gte, gt };

  struct Instruction {
    virtual ~Instruction() {};
    virtual bool contains(string v) {return false;};
  };

  struct Declaration : public Instruction {
    Variable var;
    Type type;

    bool contains(string v) {
      return var.name == v;
    };
  };

  struct ArrayAllocate : public Instruction {
    Variable lhs;
    vector<IR_t> dimensions;

    bool contains(string v) {
      for (auto dim : dimensions)
        if (dim.name == v)
          return true;
      return lhs.name == v;
    };
  };

  struct TupleAllocate : public Instruction {
    Variable lhs;
    IR_t dimension;

    bool contains(string v) {
      return (lhs.name == v || dimension.name == v);
    };
  };

  struct Assignment : public Instruction {
    Variable lhs;
    IR_s rhs;

    bool contains(string v) {
      return (lhs.name == v || rhs.name == v);
    };
  };

  struct Operation : public Instruction {
    Variable lhs;
    IR_t op_lhs;
    Operator op;
    IR_t op_rhs;

    bool contains(string v) {
      return (lhs.name == v ||
              op_lhs.name == v ||
              op_rhs.name == v);
    };
  };

  struct IndexRead : public Instruction {
    Variable lhs;
    Variable rhs;
    vector<IR_t> indices;

    bool contains(string v) {
      for (auto i : indices)
        if (i.name == v)
          return true;
      return (lhs.name == v ||
              rhs.name == v);
    };
  };

  struct IndexWrite : public Instruction {
    Variable lhs;
    IR_s rhs;
    vector<IR_t> indices;
    bool contains(string v) {
      for (auto i : indices)
        if (i.name == v)
          return true;
      return (lhs.name == v ||
              rhs.name == v);
    };
  };

  struct LengthRead : public Instruction {
    Variable lhs;
    Variable rhs;
    IR_t index;
    bool contains(string v) {
      return (lhs.name == v ||
              rhs.name == v ||
              index.name == v);
    };
  };

  struct Call : public Instruction {
    IR_callee callee;
    vector<IR_t> args;
    bool contains(string v) {
      for (auto a : args)
        if (a.name == v)
          return true;
      return (callee.name == v);
    };
  };

  struct CallAssign : public Instruction {
    Variable lhs;
    IR_callee callee;
    vector<IR_t> args;
  };

  struct Label : public Instruction {
    IR_item label;
  };

  // Basic Blocks Logic
  
  struct IR_te : public Instruction {};


  struct Branch : public IR_te {
    IR_item dest;
  };

  struct CBranch : public IR_te {
    Variable condition;
    IR_item then_dest;
    IR_item else_dest;
  };

  struct Return : public IR_te {};

  struct ReturnValue : public IR_te {
    IR_t value;
  };

  struct BasicBlock {
    IR_item entry_point;
    IR_te exit_point;
    vector<shared_ptr<Instruction>> instructions;
  };

  struct Function {
    Type return_type;
    string name;
    vector<shared_ptr<Declaration>> vars;
    vector<shared_ptr<BasicBlock>> blocks;
    map<string, shared_ptr<Declaration>> data_structs;
  };

  struct Program {
    vector<shared_ptr<Function>> functions;
    map<string, shared_ptr<Instruction>> data_structs;
  };
}
