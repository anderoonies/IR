#pragma once

#include <vector>
#include "../../L1/src/L1.h"

namespace L2 {

  struct Liveness {
    std::vector<std::set<std::string>> GEN;
    std::vector<std::set<std::string>> KILL;
    std::vector<std::set<std::string>> IN;
    std::vector<std::set<std::string>> OUT;
    std::vector<std::vector<int>> successors;
  };

  struct L2_item {
    std::string name;
    bool r;
  };

  struct L2_w : L2_item {};

  struct L2_a : L2_item {};

  struct L2_s : L2_item {};

  struct L2_x : L2_item {};

  struct L2_t : L2_item {};

  struct L2_m : L2_item {};

  struct L2_u : L2_item {};

  struct MemoryReference : L2_item {
    L2::L2_x value;
    L2::L2_m offset;
    int64_t offset_int;
  };

  struct Instruction : L1::Instruction {
    virtual ~Instruction() {};
    L2::L2_item lhs;
    L2::L2_item rhs;
    bool y_to_x_type = false;
  };

  struct GotoOperation : public Instruction{
    L2::L2_item lbl;
  };

  struct WawweOperation : public Instruction{
    L2::L2_w lhs;
    L2::L2_w start;
    L2::L2_w mult;
    int64_t e;
  };

  enum ComparisonOperator { lessthan, lessthanorequal, equal };

  struct ComparisonExpression {
    L2::L2_t lhs;
    ComparisonOperator op;
    L2::L2_t rhs;
    bool y_to_x_type = true;
  };

  struct ComparisonOperation : public Instruction{
    L2::L2_w lhs;
    ComparisonExpression cexp;
  };

  struct CjumpOperation : public Instruction{
    ComparisonExpression cexp;
    std::string then_label;
    std::string else_label;
  };

  enum ArithmeticOperator { plusequal, minusequal, timesequal, andequal };

  struct MemoryArithmeticOperation : public Instruction{
    L2::MemoryReference lhs;
    ArithmeticOperator op;
    L2::L2_t rhs;
    bool y_to_x_type = true;
  };

  struct MemoryArithmeticOperation2 : public Instruction{
    L2::L2_w lhs;
    ArithmeticOperator op;
    L2::MemoryReference rhs;
    bool y_to_x_type = true;
  };

  struct ArithmeticOperation : public Instruction{
    L2::L2_w lhs;
    ArithmeticOperator op;
    L2::L2_t rhs;
    bool y_to_x_type = true;
  };

  struct Label : public Instruction{
    std::string name;
  };

  struct FunctionCall : public Instruction{
    L2_item function_name;
    int64_t n_args;
  };

  struct RuntimeCall : public Instruction{
    L2_item function_name;
    int64_t n_args;
  };

  struct ReturnCall : public Instruction{};

  struct Assignment : public Instruction{
    L2::L2_item lhs;
    L2::L2_item rhs;
    bool y_to_x_type = true;
  };

  struct Load : public Instruction{
    L2::L2_w lhs;
    L2::MemoryReference rhs;
    bool y_to_x_type = true;
  };

  struct Store : public Instruction{
    L2::MemoryReference lhs;
    L2::L2_s rhs;
    bool y_to_x_type = true;
  };

  enum ShiftOperator { lshift, rshift };

  struct ShiftOperation : public Instruction{
    L2::L2_w lhs;
    L2::ShiftOperator op;
    L2::L2_item rhs;
    bool y_to_x_type = true;
  };

  struct Function{
    std::string name;
    int64_t arguments;
    int64_t locals;
    std::vector<L2::Instruction *> instructions;
    std::vector<std::string> variables;
  };

  struct Program : L1::Program{
    std::string entryPointLabel;
    std::vector<L2::Function *> functions;
  };

} // L2
