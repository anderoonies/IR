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

#include "L2.h"
#include "../../lib/PEGTL/pegtl.hh"
#include "../../lib/PEGTL/pegtl/analyze.hh"
#include "../../lib/PEGTL/pegtl/contrib/raw_string.hh"

using namespace pegtl;
using namespace std;

namespace L2 {

  /*
   * Grammar rules from now on.
   */

  struct L2_string_rule:
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

  struct L2_var_rule:
    L2_string_rule {};

  struct label:
    pegtl::seq<
      pegtl::one<':'>,
      L2_var_rule
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

  struct L2_label_rule:
    label {};

  struct L2_variable_rule:
    L2_var_rule {};

  struct L2_sx_rule:
    pegtl::sor<
      pegtl::string< 'r', 'c', 'x' >,
      L2_variable_rule
    > {};

  struct L2_a_rule:
    pegtl::sor<
      pegtl::string< 'r', 'd', 'i' >,
      pegtl::string< 'r', 's', 'i' >,
      pegtl::string< 'r', 'd', 'x' >,
      pegtl::string< 'r', '8' >,
      pegtl::string< 'r', '9' >,
      L2_sx_rule
    > {};

  struct L2_w_rule:
    pegtl::sor<
      pegtl::string< 'r', 'a', 'x' >,
      pegtl::string< 'r', 'b', 'x' >,
      pegtl::string< 'r', 'b', 'p' >,
      pegtl::string< 'r', '1', '0' >,
      pegtl::string< 'r', '1', '1' >,
      pegtl::string< 'r', '1', '2' >,
      pegtl::string< 'r', '1', '3' >,
      pegtl::string< 'r', '1', '4' >,
      pegtl::string< 'r', '1', '5' >,
      L2_a_rule
    > {};

  struct L2_x_rule:
    pegtl::sor<
      pegtl::string< 'r', 's', 'p' >,
      L2_w_rule
    > {};

  struct L2_s_rule:
    pegtl::sor<
      L2_x_rule,
      number,
      L2_label_rule
    > {};

  struct L2_t_rule:
    pegtl::sor<
      L2_x_rule,
      number
    > {};

  struct L2_e_rule:
    pegtl::sor<
      pegtl::one< '0' >,
      pegtl::one< '2' >,
      pegtl::one< '4' >,
      pegtl::one< '8' >
    > {};


  struct L2_u_rule:
    pegtl::sor<
      L2_w_rule,
      L2_label_rule
    > {};

  struct L2_m_rule:
    number {};

  struct L2_functioncall_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'c', 'a', 'l', 'l' >,
      seps,
      L2_u_rule,
      seps,
      functioncall_argument_number,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_runtimecall_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'c', 'a', 'l', 'l' >,
      seps,
      L2_string_rule,
      seps,
      functioncall_argument_number,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_memref_rule:
    pegtl::seq<
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'm', 'e', 'm' >,
      seps,
      L2_x_rule,
      seps,
      L2_m_rule,
      seps,
      pegtl::one< ')' >
    > {};

  struct L2_load_lhs_rule:
    L2_w_rule {};

  struct L2_load_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_load_lhs_rule,
      seps,
      arrow_rule,
      seps,
      L2_memref_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_store_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_memref_rule,
      seps,
      arrow_rule,
      seps,
      L2_s_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_assignment_rhs_rule:
    pegtl::seq<
      L2_s_rule,
      seps
    > {};

  struct L2_assignment_lhs_rule:
    pegtl::seq<
      L2_w_rule,
      seps
    >{};

  struct L2_assignment_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_assignment_lhs_rule,
      seps,
      arrow_rule,
      seps,
      L2_assignment_rhs_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_sop_rule:
    pegtl::seq<
      pegtl::sor<
        pegtl::string< '<', '<', '=' >,
        pegtl::string< '>', '>', '=' >
      >
    > {};

  struct L2_shift_rhs_rule:
    pegtl::sor<
      number,
      L2_sx_rule
    > {};

  struct L2_shift_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_w_rule,
      seps,
      L2_sop_rule,
      seps,
      L2_shift_rhs_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_aop_rule:
    pegtl::seq<
      pegtl::sor<
        pegtl::one< '+' >,
        pegtl::one< '-' >,
        pegtl::one< '*' >,
        pegtl::one< '&' >
      >,
      pegtl::one< '=' >
    > {};

  struct L2_inc_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_w_rule,
      seps,
      pegtl::string< '+', '+' >,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_dec_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_w_rule,
      pegtl::string< '-', '-' >,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_arithmetic_lhs_rule:
    pegtl::seq<
      L2_w_rule,
      seps
    > {};

  struct L2_arithmetic_rhs_rule:
    pegtl::seq<
      L2_t_rule,
      seps
    > {};

  struct L2_arithmetic_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_arithmetic_lhs_rule,
      seps,
      L2_aop_rule,
      seps,
      L2_arithmetic_rhs_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_mem_arithmetic_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_memref_rule,
      seps,
      L2_aop_rule,
      seps,
      L2_t_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_mem_arithmetic_rule_2:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_w_rule,
      seps,
      L2_aop_rule,
      seps,
      L2_memref_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_cop_rule:
    pegtl::sor<
      pegtl::string< '<', '=' >,
      pegtl::one< '<' >,
      pegtl::one< '=' >
    > {};

  struct L2_cexp_lhs_rule:
    L2_t_rule {};

  struct L2_cexp_rhs_rule:
    L2_t_rule {};

  struct L2_cmp_rule:
    pegtl::seq<
      seps,
      L2_cexp_lhs_rule,
      seps,
      L2_cop_rule,
      seps,
      L2_cexp_rhs_rule,
      seps
    > {};

  struct L2_cmp_lhs_rule:
    L2_w_rule {};

  struct L2_cmp_instruction_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_cmp_lhs_rule,
      seps,
      arrow_rule,
      seps,
      L2_cmp_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_label_instruction_rule:
    L2_label_rule {};

  struct L2_label_instruction_line_rule:
    pegtl::seq<
      seps,
      L2_label_instruction_rule,
      seps
    > {};

  struct L2_cjump_then_label_rule:
    pegtl::seq<
      L2_label_rule,
      seps
    > {};

  struct L2_cjump_else_label_rule:
    pegtl::seq<
      L2_label_rule,
      seps
    > {};

  struct L2_cjump_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'c', 'j', 'u', 'm', 'p' >,
      seps,
      L2_cmp_rule,
      seps,
      L2_cjump_then_label_rule,
      seps,
      L2_cjump_else_label_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_goto_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'g', 'o', 't', 'o' >,
      seps,
      L2_label_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_wawwe_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_w_rule,
      seps,
      pegtl::one< '@' >,
      seps,
      L2_w_rule,
      seps,
      L2_w_rule,
      seps,
      L2_e_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_return_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::string< 'r', 'e', 't', 'u', 'r', 'n' >,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_stackarg_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      L2_load_lhs_rule,
      seps,
      arrow_rule,
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::string< 's', 't', 'a', 'c', 'k', '-', 'a', 'r', 'g' >,
      seps,
      L2_m_rule,
      seps,
      pegtl::one< ')' >,
      seps,
      pegtl::one< ')' >,
      seps
    > {};


  struct L2_instruction_rule:
    pegtl::sor<
      L2_goto_rule,
      L2_cjump_rule,
      L2_return_rule,
      L2_runtimecall_rule,
      L2_functioncall_rule,
      L2_assignment_rule,
      L2_load_rule,
      L2_store_rule,
      L2_label_instruction_line_rule,
      L2_arithmetic_rule,
      L2_mem_arithmetic_rule,
      L2_mem_arithmetic_rule_2,
      L2_shift_rule,
      L2_cmp_instruction_rule,
      L2_inc_rule,
      L2_dec_rule,
      L2_wawwe_rule,
      L2_stackarg_rule
    > {};


  struct L2_instructions_rule:
    pegtl::seq<
      seps,
      pegtl::star< L2_instruction_rule >,
      seps
    > {};

  struct L2_function_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      function_name,
      seps,
      argument_number,
      seps,
      local_number,
      seps,
      L2_instructions_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L2_functions_rule:
    pegtl::seq<
      seps,
      pegtl::plus< L2_function_rule >,
      seps
    > {};

  struct entry_point_rule:
    pegtl::seq<
      seps,
      pegtl::one< '(' >,
      seps,
      pegtl::must<L2_label_rule>,
      seps,
      pegtl::must<L2_functions_rule>,
      seps,
      pegtl::one< ')' >,
      seps
    > {};


  struct grammar :
    pegtl::must<
      entry_point_rule
    > {};

  /*
   * Data structures required to parse
   */
  std::vector<L2_item> parsed_registers;
  std::vector<L2_w> parsed_w_vals;
  std::vector<int64_t> parsed_e_vals;
  std::vector<L2_a> parsed_a_vals;
  std::vector<L2_s> parsed_s_vals;
  std::vector<L2_t> parsed_t_vals;
  std::vector<L2_x> parsed_x_vals;
  std::vector<L2_m> parsed_m_vals;
  std::vector<L2_u> parsed_u_vals;
  std::vector<std::string> variables;
  std::vector<int64_t> parsed_n_vals;
  std::vector<MemoryReference> parsed_mem_refs;
  L2::ArithmeticOperator current_aop;
  L2::ShiftOperator current_sop;
  L2_w load_lhs;
  L2_w arithmetic_lhs;
  L2_t arithmetic_rhs;
  L2_w assignment_lhs;
  L2_s assignment_rhs;
  L2_item shift_rhs;
  L2_w cmp_lhs;
  L2_t current_cexp_lhs;
  L2_t current_cexp_rhs;
  L2::ComparisonOperator current_cop;
  L2::ComparisonExpression current_cexp;
  std::string cjump_then;
  std::string cjump_else;
  bool parsed_register = true;

  /*
   * Actions attached to grammar rules.
   */
  template< typename Rule >
  struct action : pegtl::nothing< Rule > {};

  template<> struct action < label > {
    static void apply( const pegtl::input & in, L2::Program & p){
    }
  };

  template<> struct action < L2_e_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      parsed_e_vals.push_back(std::stoi(in.string()));
    }
  };

  template<> struct action < function_name > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::Function *newF = new L2::Function();
      newF->name = in.string();
      p.functions.push_back(newF);
    }
  };

  template<> struct action < L2_wawwe_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::WawweOperation *wawwe = new L2::WawweOperation();
      wawwe->lhs = parsed_w_vals[parsed_w_vals.size() - 3];
      wawwe->start = parsed_w_vals[parsed_w_vals.size() - 2];
      wawwe->mult = parsed_w_vals[parsed_w_vals.size() - 1];
      wawwe->e = parsed_e_vals.back();
      p.functions.back()->instructions.push_back(wawwe);
    }
  };

  template<> struct action < L2_stackarg_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      // treat stackarg like a load but with some strings attached
      L2::Load *load = new L2::Load();
      L2::L2_x rhs;
      load->lhs = load_lhs;
      load->rhs.value.name = "rsp";
      load->rhs.offset_int = p.functions.back()->locals * 8 + std::stoi(parsed_m_vals.back().name);
      p.functions.back()->instructions.push_back(load);
    }
  };

  template<> struct action < L2_string_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2_item i;
      i.name = in.string();
      parsed_register = false;
      parsed_registers.push_back(i);
    }
  };

  template<> struct action < L2_variable_rule > {
    static void apply( const pegtl::input & in, L2::Program &p ){
      if (p.functions.size() > 0 &&
          in.string() != "print" &&
          in.string() != "array-error" &&
          in.string() != "allocate") 
      {
        p.functions.back()->variables.push_back(in.string());
      }
    }
  };

  template<> struct action < L2_label_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      if (p.entryPointLabel.empty()){
        p.entryPointLabel = in.string();
      }
      L2_item i;
      parsed_register = false;
      i.name = in.string();
      parsed_registers.push_back(i);
    }
  };

  template<> struct action < number > {
    static void apply( const pegtl::input & in, L2::Program & p){
      parsed_register = false;
    }
  };

  template<> struct action < argument_number > {
    static void apply( const pegtl::input & in, L2::Program & p){
      p.functions.back()->arguments = std::stoll(in.string());
    }
  };

  template<> struct action < local_number > {
    static void apply( const pegtl::input & in, L2::Program & p){
      p.functions.back()->locals = std::stoll(in.string());
    }
  };

  template<> struct action < functioncall_argument_number > {
    static void apply( const pegtl::input & in, L2::Program & p){
      parsed_n_vals.push_back(std::stoll(in.string()));
    }
  };

  template<> struct action < L2_w_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::L2_w newW;
      newW.name = in.string();
      newW.r = true;
      parsed_register = true;
      parsed_w_vals.push_back(newW);
    }
  };

  template<> struct action < L2_s_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::L2_s newS;
      newS.r = parsed_register;
      newS.name = in.string();
      parsed_s_vals.push_back(newS);
    }
  };

  template<> struct action < L2_t_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::L2_t newT;
      newT.r = parsed_register;
      newT.name = in.string();
      parsed_t_vals.push_back(newT);
    }
  };

  template<> struct action < L2_x_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::L2_x newX;
      newX.name = in.string();
      newX.r = true;
      parsed_register = true;
      parsed_x_vals.push_back(newX);
    }
  };

  template<> struct action < L2_m_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::L2_m newM;
      newM.name = in.string();
      parsed_m_vals.push_back(newM);
    }
  };

  template<> struct action < L2_u_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::L2_u newU;
      newU.name = in.string();
      parsed_u_vals.push_back(newU);
    }
  };

  template<> struct action < L2_label_instruction_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::Label *lbl = new L2::Label();
      lbl->name = in.string();
      p.functions.back()->instructions.push_back(lbl);
    }
  };

  template<> struct action < L2_memref_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::MemoryReference memRef;
      L2::L2_x x = parsed_x_vals.back();
      L2::L2_m m = parsed_m_vals.back();
      memRef.value = x;
      memRef.offset = m;
      memRef.offset_int = std::stoll(m.name);
      parsed_mem_refs.push_back(memRef);
    }
  };

  template<> struct action < L2_goto_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::GotoOperation *goto_op = new L2::GotoOperation();
      goto_op->lbl = parsed_registers.back();
      p.functions.back()->instructions.push_back(goto_op);
    }
  };

  template<> struct action < L2_cjump_then_label_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      cjump_then = in.string();
    }
  };

  template<> struct action < L2_cjump_else_label_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      cjump_else = in.string();
    }
  };

  template<> struct action < L2_cjump_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::CjumpOperation *cjump = new L2::CjumpOperation();
      cjump->cexp = current_cexp;
      cjump->then_label = cjump_then;
      cjump->else_label = cjump_else;
      p.functions.back()->instructions.push_back(cjump);
    }
  };

  template<> struct action < L2_cmp_lhs_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      cmp_lhs.name = in.string();
      cmp_lhs.r = parsed_register;
    }
  };

  template<> struct action < L2_cexp_lhs_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      current_cexp_lhs.name = in.string();
      current_cexp_lhs.r = parsed_register;
    }
  };

  template<> struct action < L2_cexp_rhs_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      current_cexp_rhs.name = in.string();
      current_cexp_rhs.r = parsed_register;
    }
  };

  template<> struct action < L2_cop_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
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

  template<> struct action < L2_cmp_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      current_cexp.lhs = current_cexp_lhs;
      current_cexp.rhs = current_cexp_rhs;
      current_cexp.op = current_cop;
    }
  };

  template<> struct action < L2_cmp_instruction_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::ComparisonOperation *cop = new L2::ComparisonOperation();
      cop->lhs = cmp_lhs;
      cop->cexp = current_cexp;
      p.functions.back()->instructions.push_back(cop);
    }
  };

  template<> struct action < L2_shift_rhs_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      shift_rhs.name = in.string();
      if (shift_rhs.name == "rcx") {
        shift_rhs.name = "%cl";
      }
    }
  };

  template<> struct action < L2_sop_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
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

  template<> struct action < L2_shift_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::ShiftOperation *sop = new L2::ShiftOperation();
      sop->op = current_sop;
      sop->lhs = parsed_w_vals.back();
      sop->rhs = shift_rhs;
      p.functions.back()->instructions.push_back(sop);
    }
  };

  template<> struct action < L2_aop_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
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

  template<> struct action < L2_arithmetic_lhs_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      arithmetic_lhs = parsed_w_vals.back();
    }
  };

  template<> struct action < L2_arithmetic_rhs_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      arithmetic_rhs = parsed_t_vals.back();
    }
  };

  template<> struct action < L2_arithmetic_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::ArithmeticOperation *aop = new L2::ArithmeticOperation();
      aop->op = current_aop;
      aop->lhs = arithmetic_lhs;
      aop->rhs = arithmetic_rhs;
      p.functions.back()->instructions.push_back(aop);
    }
  };

  template<> struct action < L2_inc_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::ArithmeticOperation *aop = new L2::ArithmeticOperation();
      aop->op = plusequal;
      aop->rhs.name = "1";
      aop->lhs = parsed_w_vals.back();
      p.functions.back()->instructions.push_back(aop);
    }
  };

  template<> struct action < L2_dec_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::ArithmeticOperation *aop = new L2::ArithmeticOperation();
      aop->op = minusequal;
      aop->rhs.name = "1";
      aop->lhs = parsed_w_vals.back();
      p.functions.back()->instructions.push_back(aop);
    }
  };

  template<> struct action < L2_mem_arithmetic_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::MemoryArithmeticOperation *maop = new L2::MemoryArithmeticOperation();
      L2::MemoryReference memRef = parsed_mem_refs.back();
      maop->op = current_aop;
      maop->lhs = memRef;
      maop->rhs = parsed_t_vals.back();
      p.functions.back()->instructions.push_back(maop);
    }
  };

  template<> struct action < L2_mem_arithmetic_rule_2 > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::MemoryArithmeticOperation2 *maop = new L2::MemoryArithmeticOperation2();
      L2::MemoryReference memRef = parsed_mem_refs.back();
      maop->op = current_aop;
      maop->lhs = parsed_w_vals.back();
      maop->rhs = memRef;
      p.functions.back()->instructions.push_back(maop);
    }
  };

  template<> struct action < L2_assignment_lhs_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      assignment_lhs = parsed_w_vals.back();
    }
  };

  template<> struct action < L2_assignment_rhs_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      assignment_rhs = parsed_s_vals.back();
    }
  };

  template<> struct action < L2_assignment_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::Assignment *assignment = new L2::Assignment();
      assignment->lhs = assignment_lhs;
      assignment->rhs = assignment_rhs;
      p.functions.back()->instructions.push_back(assignment);
    }
  };

  template<> struct action < L2_load_lhs_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      load_lhs = parsed_w_vals.back();
    }
  };

  template<> struct action < L2_load_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::Load *load = new L2::Load();
      load->lhs = load_lhs;
      load->rhs = parsed_mem_refs.back();
      p.functions.back()->instructions.push_back(load);
    }
  };

  template<> struct action < L2_store_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::Store *store = new L2::Store();
      store->lhs = parsed_mem_refs.back();
      store->rhs = parsed_s_vals.back();
      p.functions.back()->instructions.push_back(store);
    }
  };

  template<> struct action < L2_functioncall_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::FunctionCall *fCall = new L2::FunctionCall();
      fCall->function_name = parsed_u_vals.back();
      fCall->n_args = parsed_n_vals.back();
      p.functions.back()->instructions.push_back(fCall);
    }
  };

  template<> struct action < L2_runtimecall_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::RuntimeCall *rCall = new L2::RuntimeCall();
      rCall->function_name = parsed_registers.back();
      rCall->n_args = parsed_n_vals.back();
      p.functions.back()->instructions.push_back(rCall);
    }
  };

  template<> struct action < L2_return_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){
      L2::ReturnCall *rCall = new L2::ReturnCall();
      p.functions.back()->instructions.push_back(rCall);
    }
  };

  template<> struct action < L2_instructions_rule > {
    static void apply( const pegtl::input & in, L2::Program & p){

    }
  };

  L2::Program L2_parse_file (char *fileName){

    /*
     * Check the grammar for some possible issues.
     */
    pegtl::analyze< L2::grammar >();

    /*
     * Parse.
     */
    L2::Program p;
    pegtl::file_parser(fileName).parse< L2::grammar, L2::action >(p);

    return p;
  }

} // L2
