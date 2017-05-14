#include <string>
#include <vector>
#include <utility>
#include <algorithm>
#include <set>
#include <iterator>
#include <cstring>
#include <cctype>
#include <cstdlib>
#include <stdint.h>
#include <assert.h>

#include "L1.h"
#include "../../lib/PEGTL/pegtl.hh"
#include "../../lib/PEGTL/pegtl/analyze.hh"
#include "../../lib/PEGTL/pegtl/contrib/raw_string.hh"

using namespace pegtl;
using namespace std;

namespace L1 {

  /*
   * Grammar rules from now on.
   */

  struct L1_string_rule:
    pegtl::seq<
      pegtl::plus<
        pegtl::sor<
          pegtl::alpha,
          pegtl::one< '_' >
        >
      >,
      pegtl::star<
        pegtl::sor<
          pegtl::alpha,
          pegtl::one< '_' >,
          pegtl::digit,
          pegtl::one< '-' >
        >
      >
    > {};

  struct label:
    pegtl::seq<
      pegtl::one<':'>,
      L1_string_rule
    > {};

  struct function_name:
    label {};

  struct number:
    pegtl::seq<
      pegtl::opt<
        pegtl::sor<
          pegtl::one< '-' >,
          pegtl::one< '+' >
        >
      >,
      pegtl::plus<
        pegtl::digit
      >
    >{};

  struct argument_number:
    number {};

  struct local_number:
    number {};

  struct functioncall_argument_number:
    number {};

  struct comment:
    pegtl::disable<
      pegtl::one< ';' >,
      pegtl::until< pegtl::eolf >
    > {};

  struct seps:
    pegtl::star<
      pegtl::sor<
        pegtl::ascii::space,
        comment
      >
    > {};

  struct arrow_rule:
    pegtl::seq<
      seps,
      pegtl::one< '<' >,
      pegtl::one< '-' >,
      seps
    > {};

  struct L1_label_rule:
    label {};

  struct L1_sx_rule:
    pegtl::string< 'r', 'c', 'x' > {};

  struct L1_a_rule:
    pegtl::sor<
      pegtl::string< 'r', 'd', 'i' >,
      pegtl::string< 'r', 's', 'i' >,
      pegtl::string< 'r', 'd', 'x' >,
      L1_sx_rule,
      pegtl::string< 'r', '8' >,
      pegtl::string< 'r', '9' >
    > {};

  struct L1_w_rule:
    pegtl::sor<
      L1_a_rule,
      pegtl::string< 'r', 'a', 'x' >,
      pegtl::string< 'r', 'b', 'x' >,
      pegtl::string< 'r', 'b', 'p' >,
      pegtl::string< 'r', '1', '0' >,
      pegtl::string< 'r', '1', '1' >,
      pegtl::string< 'r', '1', '2' >,
      pegtl::string< 'r', '1', '3' >,
      pegtl::string< 'r', '1', '4' >,
      pegtl::string< 'r', '1', '5' >
    > {};

  struct L1_x_rule:
    pegtl::sor<
      L1_w_rule,
      pegtl::string< 'r', 's', 'p' >
    > {};

  struct L1_s_rule:
    pegtl::sor<
      L1_x_rule,
      number,
      L1_label_rule
    > {};

  struct L1_t_rule:
    pegtl::sor<
      L1_x_rule,
      number
    > {};

  struct L1_e_rule:
    pegtl::sor<
      pegtl::one< '0' >,
      pegtl::one< '2' >,
      pegtl::one< '4' >,
      pegtl::one< '8' >
    > {};

  struct L1_runtime_function_name:
    pegtl::sor<
      pegtl::string< 'p', 'r', 'i', 'n', 't' >,
      pegtl::string< 'a', 'l', 'l', 'o', 'c', 'a', 't', 'e' >,
      pegtl::string< 'a', 'r', 'r', 'a', 'y', '-', 'e', 'r', 'r', 'o', 'r' >
    > {};

  struct L1_u_rule:
    pegtl::sor<
      L1_w_rule,
      L1_label_rule
    > {};

  struct L1_m_rule:
    number {};

  struct L1_runtimecall_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'c', 'a', 'l', 'l' >,
      seps,
      L1_runtime_function_name,
      seps,
      functioncall_argument_number,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_functioncall_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'c', 'a', 'l', 'l' >,
      seps,
      L1_u_rule,
      seps,
      functioncall_argument_number,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_memref_rule:
    pegtl::seq<
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'm', 'e', 'm' >,
      seps,
      L1_x_rule,
      seps,
      L1_m_rule,
      seps,
      pegtl::one< ')' >
    > {};

  struct L1_load_lhs_rule:
    L1_w_rule {};

  struct L1_load_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L1_load_lhs_rule,
      seps,
      arrow_rule,
      seps,
      L1_memref_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_store_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L1_memref_rule,
      seps,
      arrow_rule,
      seps,
      L1_s_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_assignment_rhs_rule:
    pegtl::seq<
      L1_s_rule,
      seps
    > {};

  struct L1_assignment_lhs_rule:
    pegtl::seq<
      L1_w_rule,
      seps
    >{};

  struct L1_assignment_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L1_assignment_lhs_rule,
      seps,
      arrow_rule,
      seps,
      L1_assignment_rhs_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_sop_rule:
    pegtl::seq<
      pegtl::sor<
        pegtl::string< '<', '<', '=' >,
        pegtl::string< '>', '>', '=' >
      >
    > {};

  struct L1_shift_rhs_rule:
    pegtl::sor<
      number,
      L1_sx_rule
    > {};

  struct L1_shift_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L1_w_rule,
      seps,
      L1_sop_rule,
      seps,
      L1_shift_rhs_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_aop_rule:
    pegtl::seq<
      pegtl::sor<
        pegtl::one< '+' >,
        pegtl::one< '-' >,
        pegtl::one< '*' >,
        pegtl::one< '&' >
      >,
      pegtl::one< '=' >
    > {};

  struct L1_inc_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L1_w_rule,
      pegtl::string< '+', '+' >,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_dec_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L1_w_rule,
      pegtl::string< '-', '-' >,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_arithmetic_lhs_rule:
    pegtl::seq<
      L1_w_rule,
      seps
    > {};

  struct L1_arithmetic_rhs_rule:
    pegtl::seq<
      L1_t_rule,
      seps
    > {};

  struct L1_arithmetic_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L1_arithmetic_lhs_rule,
      seps,
      L1_aop_rule,
      seps,
      L1_arithmetic_rhs_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_mem_arithmetic_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L1_memref_rule,
      seps,
      L1_aop_rule,
      seps,
      L1_t_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_mem_arithmetic_rule_2:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L1_w_rule,
      seps,
      L1_aop_rule,
      seps,
      L1_memref_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_cop_rule:
    pegtl::sor<
      pegtl::string< '<', '=' >,
      pegtl::one< '<' >,
      pegtl::one< '=' >
    > {};

  struct L1_cexp_lhs_rule:
    L1_t_rule {};

  struct L1_cexp_rhs_rule:
    L1_t_rule {};

  struct L1_cmp_rule:
    pegtl::seq<
      seps,
      L1_cexp_lhs_rule,
      seps,
      L1_cop_rule,
      seps,
      L1_cexp_rhs_rule,
      seps
    > {};

  struct L1_cmp_lhs_rule:
    L1_w_rule {};

  struct L1_cmp_instruction_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L1_cmp_lhs_rule,
      seps,
      arrow_rule,
      seps,
      L1_cmp_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_label_instruction_rule:
    L1_label_rule {};

  struct L1_label_instruction_line_rule:
    pegtl::seq<
      seps,
      L1_label_instruction_rule,
      seps
    > {};

  struct L1_cjump_then_label_rule:
    pegtl::seq<
      L1_label_rule,
      seps
    > {};

  struct L1_cjump_else_label_rule:
    pegtl::seq<
      L1_label_rule,
      seps
    > {};

  struct L1_cjump_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'c', 'j', 'u', 'm', 'p' >,
      seps,
      L1_cmp_rule,
      seps,
      L1_cjump_then_label_rule,
      seps,
      L1_cjump_else_label_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_goto_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'g', 'o', 't', 'o' >,
      seps,
      L1_label_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_wawwe_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L1_w_rule,
      seps,
      pegtl::one< '@' >,
      seps,
      L1_w_rule,
      seps,
      L1_w_rule,
      seps,
      L1_e_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_return_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'r', 'e', 't', 'u', 'r', 'n' >,
      seps,
      pegtl::one< ')' >,
      seps
    > {};


  struct L1_instruction_rule:
    pegtl::sor<
      L1_assignment_rule,
      L1_functioncall_rule,
      L1_runtimecall_rule,
      L1_load_rule,
      L1_store_rule,
      L1_label_instruction_line_rule,
      L1_arithmetic_rule,
      L1_mem_arithmetic_rule,
      L1_mem_arithmetic_rule_2,
      L1_shift_rule,
      L1_cmp_instruction_rule,
      L1_cjump_rule,
      L1_goto_rule,
      L1_inc_rule,
      L1_dec_rule,
      L1_wawwe_rule,
      L1_return_rule
    > {};


  struct L1_instructions_rule:
    pegtl::seq<
      seps,
      pegtl::star< L1_instruction_rule >,
      seps
    > {};

  struct L1_function_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      function_name,
      seps,
      argument_number,
      seps,
      local_number,
      seps,
      pegtl::must<L1_instructions_rule>,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L1_functions_rule:
    pegtl::seq<
      seps,
      pegtl::plus< L1_function_rule >,
      seps
    > {};

  struct entry_point_rule:
    pegtl::seq<
      seps,
      pegtl::must<pegtl::one<'('>>,
      seps,
      pegtl::must<L1_label_rule>,
      seps,
      pegtl::must<L1_functions_rule>,
      seps,
      pegtl::one<')'>,
      seps
    > {};

  struct grammar :
    pegtl::must<
      entry_point_rule
    > {};

  /*
   * Data structures required to parse
   */
  std::vector<L1_item> parsed_registers;
  std::vector<L1_w> parsed_w_vals;
  std::vector<int64_t> parsed_e_vals;
  std::vector<L1_a> parsed_a_vals;
  std::vector<L1_s> parsed_s_vals;
  std::vector<L1_t> parsed_t_vals;
  std::vector<L1_x> parsed_x_vals;
  std::vector<L1_m> parsed_m_vals;
  std::vector<L1_u> parsed_u_vals;
  std::vector<int64_t> parsed_n_vals;
  std::vector<MemoryReference> parsed_mem_refs;
  L1::ArithmeticOperator current_aop;
  L1::ShiftOperator current_sop;
  L1_w load_lhs;
  L1_w arithmetic_lhs;
  L1_t arithmetic_rhs;
  L1_w assignment_lhs;
  L1_s assignment_rhs;
  L1_item shift_rhs;
  L1_w cmp_lhs;
  L1_t current_cexp_lhs;
  L1_t current_cexp_rhs;
  L1::ComparisonOperator current_cop;
  L1::ComparisonExpression current_cexp;
  std::string cjump_then;
  std::string cjump_else;
  bool parsed_register = true;

  /*
   * Actions attached to grammar rules.
   */
  template< typename Rule >
  struct action : pegtl::nothing< Rule > {};

  template<> struct action < label > {
    static void apply( const pegtl::input & in, L1::Program & p){
    }
  };

  template<> struct action < L1_e_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      parsed_e_vals.push_back(std::stoi(in.string()));
    }
  };

  template<> struct action < function_name > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::Function *newF = new L1::Function();
      newF->name = in.string();
      p.functions.push_back(newF);
    }
  };

  template<> struct action < L1_wawwe_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::WawweOperation *wawwe = new L1::WawweOperation();
      wawwe->lhs = parsed_w_vals[parsed_w_vals.size() - 3];
      wawwe->start = parsed_w_vals[parsed_w_vals.size() - 2];
      wawwe->mult = parsed_w_vals[parsed_w_vals.size() - 1];
      wawwe->e = parsed_e_vals.back();
      p.functions.back()->instructions.push_back(wawwe);
    }
  };

  template<> struct action < L1_string_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1_item i;
      i.name = in.string();
      parsed_register = false;
      parsed_registers.push_back(i);
    }
  };

  template<> struct action < L1_label_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      if (p.entryPointLabel.empty()){
        p.entryPointLabel = in.string();
      }
      L1_item i;
      i.name = in.string().replace(0,1,"_");
      parsed_registers.push_back(i);
    }
  };

  template<> struct action < number > {
    static void apply( const pegtl::input & in, L1::Program & p){
      parsed_register = false;
    }
  };

  template<> struct action < argument_number > {
    static void apply( const pegtl::input & in, L1::Program & p){
      p.functions.back()->arguments = std::stoll(in.string());
    }
  };

  template<> struct action < local_number > {
    static void apply( const pegtl::input & in, L1::Program & p){
      p.functions.back()->locals = std::stoll(in.string());
    }
  };

  template<> struct action < functioncall_argument_number > {
    static void apply( const pegtl::input & in, L1::Program & p){
      parsed_n_vals.push_back(std::stoll(in.string()));
    }
  };

  template<> struct action < L1_w_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::L1_w newW;
      newW.name = in.string();
      newW.r = true;
      parsed_register = true;
      parsed_w_vals.push_back(newW);
    }
  };

  template<> struct action < L1_s_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::L1_s newS;
      newS.r = parsed_register;
      newS.name = in.string();
      if (newS.name[0] == ':') {
        newS.name[0] = '_';
      }
      parsed_s_vals.push_back(newS);
    }
  };

  template<> struct action < L1_t_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::L1_t newT;
      newT.r = parsed_register;
      newT.name = in.string();
      parsed_t_vals.push_back(newT);
    }
  };

  template<> struct action < L1_x_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::L1_x newX;
      newX.name = in.string();
      newX.r = true;
      parsed_register = true;
      parsed_x_vals.push_back(newX);
    }
  };

  template<> struct action < L1_m_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::L1_m newM;
      newM.name = in.string();
      parsed_m_vals.push_back(newM);
    }
  };

  template<> struct action < L1_u_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::L1_u newU;
      newU.name = in.string();
      if (newU.name[0] == ':') {
        newU.name[0] = '_';
      }
      parsed_u_vals.push_back(newU);
    }
  };

  template<> struct action < L1_label_instruction_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::Label *lbl = new L1::Label();
      lbl->name = in.string().replace(0,1, "_");
      p.functions.back()->instructions.push_back(lbl);
    }
  };

  template<> struct action < L1_memref_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::MemoryReference memRef;
      L1::L1_x x = parsed_x_vals.back();
      L1::L1_m m = parsed_m_vals.back();
      memRef.value = x;
      memRef.offset = m;
      memRef.offset_int = std::stoll(m.name);
      parsed_mem_refs.push_back(memRef);
    }
  };

  template<> struct action < L1_goto_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::GotoOperation *goto_op = new L1::GotoOperation();
      goto_op->lbl = parsed_registers.back();
      p.functions.back()->instructions.push_back(goto_op);
    }
  };

  template<> struct action < L1_cjump_then_label_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      cjump_then = parsed_registers.back().name;
    }
  };

  template<> struct action < L1_cjump_else_label_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      cjump_else = parsed_registers.back().name;
    }
  };

  template<> struct action < L1_cjump_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::CjumpOperation *cjump = new L1::CjumpOperation();
      cjump->cexp = current_cexp;
      cjump->then_label = cjump_then;
      cjump->else_label = cjump_else;
      p.functions.back()->instructions.push_back(cjump);
    }
  };

  template<> struct action < L1_cmp_lhs_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      cmp_lhs.name = in.string();
      cmp_lhs.r = parsed_register;
    }
  };

  template<> struct action < L1_cexp_lhs_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      current_cexp_lhs.name = in.string();
      current_cexp_lhs.r = parsed_register;
    }
  };

  template<> struct action < L1_cexp_rhs_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      current_cexp_rhs.name = in.string();
      current_cexp_rhs.r = parsed_register;
    }
  };

  template<> struct action < L1_cop_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      std::string op_string = in.string();
      std::string lt ("<");
      std::string lte ("<=");
      std::string eq ("=");
      if (op_string.compare(lt) == 0) {
        current_cop = lessthan;
      }
      else if (op_string.compare(lte) == 0) {
        current_cop = lessthanorequal;
      }
      else if (op_string.compare(eq) == 0) {
        current_cop = equal;
      }
    }
  };

  template<> struct action < L1_cmp_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      current_cexp.lhs = current_cexp_lhs;
      current_cexp.rhs = current_cexp_rhs;
      current_cexp.op = current_cop;
    }
  };

  template<> struct action < L1_cmp_instruction_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::ComparisonOperation *cop = new L1::ComparisonOperation();
      cop->lhs = cmp_lhs;
      cop->cexp = current_cexp;
      p.functions.back()->instructions.push_back(cop);
    }
  };

  template<> struct action < L1_shift_rhs_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      shift_rhs.name = in.string();
      if (shift_rhs.name == "rcx") {
        shift_rhs.name = "%cl";
      } else {
        shift_rhs.name = "$" + in.string();
      }
    }
  };

  template<> struct action < L1_sop_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      std::string op_string = in.string();
      std::string ls ("<<=");
      std::string rs (">>=");
      if (op_string.compare(ls) == 0) {
        current_sop = lshift;
      }
      else if (op_string.compare(rs) == 0) {
        current_sop = rshift;
      }
    }
  };

  template<> struct action < L1_shift_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::ShiftOperation *sop = new L1::ShiftOperation();
      sop->op = current_sop;
      sop->lhs = parsed_w_vals.back();
      sop->rhs = shift_rhs;
      p.functions.back()->instructions.push_back(sop);
    }
  };

  template<> struct action < L1_aop_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      std::string op_string = in.string();
      std::string peq ("+=");
      std::string meq ("-=");
      std::string teq ("*=");
      std::string aeq ("&=");
      if (op_string.compare(peq) == 0) {
        current_aop = plusequal;
      }
      else if (op_string.compare(meq) == 0) {
        current_aop = minusequal;
      }
      else if (op_string.compare(teq) == 0) {
        current_aop = timesequal;
      }
      else if (op_string.compare(aeq) == 0) {
        current_aop = andequal;
      }
      else {
        cerr << "error" << endl;
      }
    }
  };

  template<> struct action < L1_arithmetic_lhs_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      arithmetic_lhs = parsed_w_vals.back();
    }
  };

  template<> struct action < L1_arithmetic_rhs_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      arithmetic_rhs = parsed_t_vals.back();
    }
  };

  template<> struct action < L1_arithmetic_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::ArithmeticOperation *aop = new L1::ArithmeticOperation();
      aop->op = current_aop;
      aop->lhs = arithmetic_lhs;
      aop->rhs = arithmetic_rhs;
      p.functions.back()->instructions.push_back(aop);
    }
  };

  template<> struct action < L1_inc_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::ArithmeticOperation *aop = new L1::ArithmeticOperation();
      aop->op = plusequal;
      aop->rhs.name = "1";
      aop->lhs = parsed_w_vals.back();
      p.functions.back()->instructions.push_back(aop);
    }
  };

  template<> struct action < L1_dec_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::ArithmeticOperation *aop = new L1::ArithmeticOperation();
      aop->op = minusequal;
      aop->rhs.name = "1";
      aop->lhs = parsed_w_vals.back();
      p.functions.back()->instructions.push_back(aop);
    }
  };

  template<> struct action < L1_mem_arithmetic_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::MemoryArithmeticOperation *maop = new L1::MemoryArithmeticOperation();
      L1::MemoryReference memRef = parsed_mem_refs.back();
      maop->op = current_aop;
      maop->lhs = memRef;
      maop->rhs = parsed_t_vals.back();
      p.functions.back()->instructions.push_back(maop);
    }
  };

  template<> struct action < L1_mem_arithmetic_rule_2 > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::MemoryArithmeticOperation2 *maop = new L1::MemoryArithmeticOperation2();
      L1::MemoryReference memRef = parsed_mem_refs.back();
      maop->op = current_aop;
      maop->lhs = parsed_w_vals.back();
      maop->rhs = memRef;
      p.functions.back()->instructions.push_back(maop);
    }
  };

  template<> struct action < L1_assignment_lhs_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      assignment_lhs = parsed_w_vals.back();
    }
  };

  template<> struct action < L1_assignment_rhs_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      assignment_rhs = parsed_s_vals.back();
    }
  };

  template<> struct action < L1_assignment_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::Assignment *assignment = new L1::Assignment();
      assignment->lhs = assignment_lhs;
      assignment->rhs = assignment_rhs;
      p.functions.back()->instructions.push_back(assignment);
    }
  };

  template<> struct action < L1_load_lhs_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      load_lhs = parsed_w_vals.back();
    }
  };

  template<> struct action < L1_load_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::Load *load = new L1::Load();
      load->lhs = load_lhs;
      load->rhs = parsed_mem_refs.back();
      p.functions.back()->instructions.push_back(load);
    }
  };

  template<> struct action < L1_store_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::Store *store = new L1::Store();
      store->lhs = parsed_mem_refs.back();
      store->rhs = parsed_s_vals.back();
      p.functions.back()->instructions.push_back(store);
    }
  };

  template<> struct action < L1_runtime_function_name > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1_item i;
      i.name = in.string();
      parsed_register = false;
      parsed_registers.push_back(i);
    }
  };

  template<> struct action < L1_runtimecall_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::RuntimeCall *rCall = new L1::RuntimeCall();
      rCall->function_name = parsed_registers.back();
      if (rCall->function_name.name == "array-error") {
        rCall->function_name.name = "array_error";
      }
      rCall->n_args = parsed_n_vals.back();
      p.functions.back()->instructions.push_back(rCall);
    }
  };

  template<> struct action < L1_functioncall_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::FunctionCall *fCall = new L1::FunctionCall();
      fCall->function_name = parsed_u_vals.back();
      fCall->n_args = parsed_n_vals.back();
      p.functions.back()->instructions.push_back(fCall);
    }
  };

  template<> struct action < L1_return_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){
      L1::ReturnCall *rCall = new L1::ReturnCall();
      p.functions.back()->instructions.push_back(rCall);
    }
  };

  template<> struct action < L1_instructions_rule > {
    static void apply( const pegtl::input & in, L1::Program & p){

    }
  };

  L1::Program L1_parse_file (char *fileName){

    /*
     * Check the grammar for some possible issues.
     */
    pegtl::analyze< L1::grammar >();

    /*
     * Parse.
     */
    L1::Program p;
    pegtl::file_parser(fileName).parse< L1::grammar, L1::action >(p);

    return p;
  }

} // L1
