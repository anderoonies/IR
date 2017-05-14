#pragma once

#include <vector>
#include <string>

namespace L3 {
  extern std::vector<std::string> caller_save_registers;

  extern std::vector<std::string> callee_save_registers;

  extern std::vector<std::string> arg_registers;

  struct L3_item {
    std::string name;

    bool operator==(const L3_item &other) const {
      return name == other.name;
    }
  };

  struct Variable : public L3_item {
  };

  struct L3_s : L3_item {
  };

  struct L3_t : L3_item {
  };

  struct L3_u : L3_item {
  };

  struct L3_callee : L3_item {
  };

  enum Operation { plus, minus, times, l3and, lshift, rshift };

  enum Comparator { lt, lte, eq, gte, gt };

  struct Instruction {
    virtual ~Instruction() {};
  };

  struct Assignment : public Instruction {
    Variable lhs;
    L3_s rhs;
  };

  struct Arithmetic : public Instruction {
    Variable lhs;
    Operation arith_op;
    L3_t arith_lhs;
    L3_t arith_rhs;
  };

  struct Comparison : public Instruction {
    Variable lhs;
    Comparator comp_op;
    L3_t comp_lhs;
    L3_t comp_rhs;
  };

  struct Load : public Instruction {
    Variable lhs;
    Variable rhs;
  };

  struct Store : public Instruction {
    Variable lhs;
    L3_s rhs;
  };

  struct Branch : public Instruction {
    L3_item dest;
  };

  struct Label : public Instruction {
    L3_item label;
  };

  struct CBranch : public Instruction {
    Variable condition;
    L3_item then_dest;
    L3_item else_dest;
  };

  struct Return : public Instruction {
  };

  struct ReturnValue : public Instruction {
    L3_t value;
  };

  struct Call : public Instruction {
    L3_callee callee;
    std::vector<L3_t> args;
  };

  struct CallAssign : public Call {
    Variable lhs;
    L3_callee callee;
    std::vector<L3_t> args;
  };

  struct Function {
    std::string name;
    std::vector<L3_t> args;
    std::vector<Instruction *> instructions;
  };

  struct Program {
    std::vector<Function *> functions;
  };
}
