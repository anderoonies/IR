#pragma once

#include <vector>

namespace L1 {

  struct L1_item {
    std::string name;
    bool r;
  };

  struct L1_w : L1_item {};

  struct L1_a : L1_item {};

  struct L1_s : L1_item {};

  struct L1_x : L1_item {};

  struct L1_t : L1_item {};

  struct L1_m : L1_item {};

  struct L1_u : L1_item {};

  struct MemoryReference{
    L1::L1_x value;
    L1::L1_m offset;
    int64_t offset_int;
  };

  struct Instruction {
    virtual ~Instruction() {};
  };

  struct GotoOperation : public Instruction{
    L1::L1_item lbl;
  };

  struct WawweOperation : public Instruction{
    L1::L1_w lhs;
    L1::L1_w start;
    L1::L1_w mult;
    int64_t e;
  };

  enum ComparisonOperator { lessthan, lessthanorequal, equal };

  struct ComparisonExpression {
    L1::L1_t lhs;
    ComparisonOperator op;
    L1::L1_t rhs;
  };

  struct ComparisonOperation : public Instruction{
    L1::L1_w lhs;
    ComparisonExpression cexp;
  };

  struct CjumpOperation : public Instruction{
    ComparisonExpression cexp;
    std::string then_label;
    std::string else_label;
  };

  enum ArithmeticOperator { plusequal, minusequal, timesequal, andequal };

  struct MemoryArithmeticOperation : public Instruction{
    L1::MemoryReference lhs;
    ArithmeticOperator op;
    L1::L1_t rhs;
  };

  struct MemoryArithmeticOperation2 : public Instruction{
    L1::L1_w lhs;
    ArithmeticOperator op;
    L1::MemoryReference rhs;
  };

  struct ArithmeticOperation : public Instruction{
    L1::L1_w lhs;
    ArithmeticOperator op;
    L1::L1_t rhs;
  };

  struct Label : public Instruction{
    std::string name;
  };

  struct FunctionCall : public Instruction{
    L1_item function_name;
    int64_t n_args;
  };

  struct RuntimeCall : public Instruction{
    L1_item function_name;
    int64_t n_args;
  };

  struct ReturnCall : public Instruction{};

  struct Assignment : public Instruction{
    L1::L1_w lhs;
    L1::L1_s rhs;
  };

  struct Load : public Instruction{
    L1::L1_w lhs;
    L1::MemoryReference rhs;
  };

  struct Store : public Instruction{
    L1::MemoryReference lhs;
    L1::L1_s rhs;
  };

  enum ShiftOperator { lshift, rshift };

  struct ShiftOperation : public Instruction{
    L1::L1_w lhs;
    L1::ShiftOperator op;
    L1::L1_item rhs;
  };

  struct Function{
    std::string name;
    int64_t arguments;
    int64_t locals;
    std::vector<L1::Instruction *> instructions;
  };

  struct Program{
    std::string entryPointLabel;
    std::vector<L1::Function *> functions;
  };

} // L1
