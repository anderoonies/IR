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

#include "L3.h"
#include "../../lib/PEGTL/pegtl.hh"
#include "../../lib/PEGTL/pegtl/analyze.hh"

using namespace pegtl;
using namespace std;

namespace L3 {

  /*
   * Grammar rules from now on.
   */

  struct number :
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
    > {};

  struct comment :
    pegtl::disable<
      pegtl::one< ';' >,
      pegtl::until< pegtl::eolf >
    > {};

  struct seps :
    pegtl::star<
      pegtl::sor<
        pegtl::ascii::space,
        comment
      >
    > {};

  struct L3_arrow_rule :
    pegtl::seq<
      seps,
      pegtl::one< '<' >,
      pegtl::one< '-' >,
      seps
    > {};

  struct L3_var_rule :
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

  struct L3_label_rule :
    pegtl::seq<
      pegtl::one< ':' >,
      L3_var_rule
    > {};

  struct L3_cop_rule :
    pegtl::sor<
      pegtl::string< '<' >,
      pegtl::string< '<', '=' >,
      pegtl::string< '=' >,
      pegtl::string< '>', '=' >,
      pegtl::string< '>' >
    > {};

  struct L3_op_rule :
    pegtl::sor<
      pegtl::string< '+' >,
      pegtl::string< '-' >,
      pegtl::string< '*' >,
      pegtl::string< '&' >,
      pegtl::string< '<', '<' >,
      pegtl::string< '>', '>' >
    > {};

  struct L3_u_rule :
    pegtl::sor<
      L3_var_rule,
      L3_label_rule
    > {};

  struct L3_t_rule :
    pegtl::sor<
      L3_var_rule,
      number
    > {};

  struct L3_s_rule :
    pegtl::sor<
      L3_t_rule,
      L3_label_rule
    > {};

  struct L3_vars_rule :
    pegtl::sor<
      pegtl::seq<
        L3_t_rule,
        pegtl::star<
          pegtl::one< ',' >,
          seps,
          L3_t_rule
        >
      >,
      L3_t_rule,
      seps
    > {};

  struct L3_args_rule :
    pegtl::sor<
      pegtl::seq<
        L3_t_rule,
        pegtl::star<
          pegtl::one< ',' >,
          seps,
          L3_t_rule
        >
      >,
      L3_t_rule,
      seps
    > {};

  struct L3_callee_rule :
    pegtl::sor<
      L3_u_rule,
      pegtl::string< 'p','r','i','n','t' >,
      pegtl::string< 'a','l','l','o','c','a','t','e' >,
      pegtl::string< 'a','r','r','a','y','-','e','r','r','o','r' >
    > {};

  struct L3_assignment_rule :
    pegtl::seq<
      seps,
      L3_var_rule,
      seps,
      L3_arrow_rule,
      seps,
      L3_s_rule,
      seps
    > {};

  struct L3_arithmetic_rule :
    pegtl::seq<
      seps,
      L3_var_rule,
      seps,
      L3_arrow_rule,
      seps,
      L3_t_rule,
      seps,
      L3_op_rule,
      seps,
      L3_t_rule,
      seps
    > {};

  struct L3_comparison_rule :
    pegtl::seq<
      seps,
      L3_var_rule,
      seps,
      L3_arrow_rule,
      seps,
      L3_t_rule,
      seps,
      L3_cop_rule,
      seps,
      L3_t_rule,
      seps
    > {};

  struct L3_load_rule :
    pegtl::seq<
      seps,
      L3_var_rule,
      seps,
      L3_arrow_rule,
      seps,
      pegtl::string< 'l','o','a','d' >,
      seps,
      L3_var_rule,
      seps
    > {};

  struct L3_store_rule :
    pegtl::seq<
      seps,
      pegtl::string< 's','t','o','r','e' >,
      seps,
      L3_var_rule,
      seps,
      L3_arrow_rule,
      seps,
      L3_s_rule,
      seps
    > {};

  struct L3_branch_rule :
    pegtl::seq<
      seps,
      pegtl::string< 'b','r' >,
      seps,
      L3_label_rule,
      seps
    > {};

  struct L3_i_label_rule:
    L3_label_rule {};

  struct L3_conditional_branch_rule :
    pegtl::seq<
      seps,
      pegtl::string< 'b','r' >,
      seps,
      L3_var_rule,
      seps,
      L3_label_rule,
      seps,
      L3_label_rule,
      seps
    > {};

  struct L3_return_rule :
    pegtl::seq<
      seps,
      pegtl::string< 'r','e','t','u','r','n' >,
      seps
    > {};

  struct L3_returnvalue_rule :
    pegtl::seq<
      seps,
      pegtl::string< 'r','e','t','u','r','n' >,
      seps,
      L3_t_rule,
      seps
    > {};

  struct L3_call_rule :
    pegtl::seq<
      seps,
      pegtl::string< 'c','a','l','l' >,
      seps,
      L3_callee_rule,
      seps,
      pegtl::one< '(' >,
      seps,
      L3_args_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L3_call_assign_rule :
    pegtl::seq<
      seps,
      L3_var_rule,
      seps,
      L3_arrow_rule,
      seps,
      pegtl::string< 'c','a','l','l' >,
      seps,
      L3_callee_rule,
      seps,
      pegtl::one< '(' >,
      seps,
      L3_args_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct L3_instruction_rule :
    pegtl::sor<
      L3_conditional_branch_rule,
      L3_load_rule,
      L3_store_rule,
      L3_call_assign_rule,
      L3_call_rule,
      L3_comparison_rule,
      L3_arithmetic_rule,
      L3_assignment_rule,
      L3_branch_rule,
      L3_i_label_rule,
      L3_returnvalue_rule,
      L3_return_rule
    > {};

  struct L3_instructions_rule :
    pegtl::star<
      seps,
      L3_instruction_rule,
      seps
    > {};

  struct L3_function_name_rule :
    pegtl::seq<
      L3_label_rule 
    > {};

  struct L3_function_rule :
    pegtl::seq<
      pegtl::string< 'd','e','f','i','n','e' >,
      seps,
      L3_function_name_rule,
      seps,
      pegtl::one< '(' >,
      seps,
      L3_vars_rule,
      seps,
      pegtl::one< ')' >,
      seps,
      pegtl::one< '{' >,
      seps,
      L3_instructions_rule,
      seps,
      pegtl::one< '}' >,
      seps
    > {};

  struct L3_program_rule :
    pegtl::star<
      L3_function_rule
    > {};

  struct entry_point_rule :
    pegtl::must<
      pegtl::star<
        L3_function_rule
      >
    > {};

  struct grammar :
    pegtl::must<
      entry_point_rule
    > {};

  /////////////
  //   DATA  //
  /////////////
  
  std::vector<L3::Function *> parsed_functions;
  std::vector<L3::Variable *> parsed_variables;
  std::vector<L3::L3_s> parsed_s_vals;
  std::vector<L3::L3_t> parsed_t_vals;
  std::vector<L3::L3_u> parsed_u_vals;
  std::vector<L3::L3_t> parsed_args;
  L3::L3_callee parsed_callee;
  std::vector<std::string> parsed_strings;
  L3::Operation parsed_op;
  L3::Comparator parsed_cop;

  /////////////
  // ACTIONS //
  /////////////
  
  void clear_memory() {
    parsed_variables.clear();
    parsed_s_vals.clear();
    parsed_t_vals.clear();
    parsed_u_vals.clear();
    parsed_strings.clear();
    parsed_args.clear();
  }
  
  template< typename Rule >
    struct action : pegtl::nothing< Rule > {};
  
  template<> struct action < L3_label_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      parsed_strings.push_back(in.string()); 
    }
  };

  template<> struct action < L3_cop_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      std::string cop = in.string();
      std::string lt ("<");
      std::string lte ("<=");
      std::string eq ("=");
      std::string gte (">=");
      std::string gt (">");
      if (cop.compare(lt) == 0)
        parsed_cop = L3::lt;
      else if (cop.compare(lte) == 0)
        parsed_cop = L3::lte;
      else if (cop.compare(eq) == 0)
        parsed_cop = L3::eq;
      else if (cop.compare(gte) == 0)
        parsed_cop = L3::gte;
      else if (cop.compare(gt) == 0)
        parsed_cop = L3::gt;
    }
  };

  template<> struct action < L3_op_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      std::string op = in.string();
      std::string plus ("+");
      std::string minus ("-");
      std::string times ("*");
      std::string l3and ("&");
      std::string lshift ("<<");
      std::string rshift (">>");
      if (op.compare(plus) == 0)
        parsed_op = L3::plus;
      else if (op.compare(minus) == 0)
        parsed_op = L3::minus;
      else if (op.compare(times) == 0)
        parsed_op = L3::times;
      else if (op.compare(l3and) == 0)
        parsed_op = L3::l3and;
      else if (op.compare(lshift) == 0)
        parsed_op = L3::lshift;
      else if (op.compare(rshift) == 0)
        parsed_op = L3::rshift;
    }
  };

  template<> struct action < L3_s_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::L3_s s;
      s.name = in.string();
      parsed_s_vals.push_back(s);
    }
  };

  template<> struct action < L3_t_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::L3_t t;
      t.name = in.string();
      parsed_t_vals.push_back(t);
    }
  };

  template<> struct action < L3_u_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::L3_u u;
      u.name = in.string();
      parsed_u_vals.push_back(u);
    }
  };

  template<> struct action < L3_var_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::Variable *var = new L3::Variable();
      var->name = in.string();
      parsed_variables.push_back(var);
    }
  };

  template<> struct action < L3_args_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      // args are a property of a function call.
      parsed_args.insert(
          parsed_args.end(),
          parsed_t_vals.begin(),
          parsed_t_vals.end()
      );
      for (int i = 0; i < parsed_args.size(); i++) {
        L3::Assignment *arg_assn = new L3::Assignment;
        arg_assn->lhs.name = arg_registers[i]; 
        arg_assn->rhs.name = parsed_args[i].name;
        p.functions.back()->instructions.push_back(arg_assn);
      }
    }
  };

  template<> struct action < L3_vars_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      // vars are a property of a function itself.
      L3::Function *currentFunction = p.functions.back();
      currentFunction->args.insert(
          currentFunction->args.end(),
          parsed_t_vals.begin(),
          parsed_t_vals.end()
      );
      for (int i = 0; i < currentFunction->args.size(); i++) {
        L3::Assignment *arg_assn = new L3::Assignment;
        arg_assn->lhs.name = currentFunction->args[i].name;
        arg_assn->rhs.name = arg_registers[i];
        currentFunction->instructions.push_back(arg_assn);
      }
      clear_memory();
    }
  };

  template<> struct action < L3_callee_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::L3_callee callee;
      callee.name = in.string();
      parsed_callee = callee;
    }
  };

  template<> struct action < L3_assignment_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::Variable lhs = *parsed_variables.at(0);
      L3::L3_s rhs = parsed_s_vals.back();
      L3::Assignment *assignment = new L3::Assignment();
      assignment->lhs = lhs;
      assignment->rhs = rhs;
      p.functions.back()->instructions.push_back(assignment);
      clear_memory();
    }
  };

  template<> struct action < L3_arithmetic_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::Arithmetic *arithmetic = new L3::Arithmetic();
      L3::Variable lhs = *parsed_variables.at(0);
      arithmetic->lhs = lhs;
      arithmetic->arith_lhs = parsed_t_vals.end()[-2];
      arithmetic->arith_rhs = parsed_t_vals.end()[-1];
      arithmetic->arith_op = parsed_op;
      p.functions.back()->instructions.push_back(arithmetic);
      clear_memory();
    }
  };

  template<> struct action < L3_comparison_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::Variable lhs = *parsed_variables.at(0);
      L3::Comparison *comparison = new L3::Comparison();
      comparison->lhs = lhs;
      comparison->comp_lhs = parsed_t_vals.end()[-2];
      comparison->comp_rhs = parsed_t_vals.end()[-1];
      comparison->comp_op = parsed_cop;
      p.functions.back()->instructions.push_back(comparison);
      clear_memory();
    }
  };

  template<> struct action < L3_load_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::Variable lhs = *parsed_variables.at(0);
      L3::Variable rhs = *parsed_variables.at(1);
      L3::Load *load = new L3::Load();
      load->lhs = lhs;
      load->rhs = rhs;
      p.functions.back()->instructions.push_back(load);
      clear_memory();
    }
  };

  template<> struct action < L3_store_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      // index 0 is "store"
      L3::Variable lhs = *parsed_variables.at(1);
      L3::L3_s rhs = parsed_s_vals.back();
      L3::Store *store = new L3::Store();
      store->lhs = lhs;
      store->rhs = rhs;
      p.functions.back()->instructions.push_back(store);
      clear_memory();
    }
  };

  template<> struct action < L3_branch_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::Branch *branch = new L3::Branch();
      L3::L3_item dest;
      dest.name = parsed_strings.back();
      branch->dest = dest;
      p.functions.back()->instructions.push_back(branch);
      clear_memory();
    }
  };

  template<> struct action < L3_i_label_rule >{
      static void apply( const pegtl::input &in, L3::Program &p){
        L3::Label *label = new L3::Label();
        L3::L3_item lbl;
        lbl.name = parsed_variables.back()->name;
        label->label = lbl;
        p.functions.back()->instructions.push_back(label);
        clear_memory();
      }
  };

  template<> struct action < L3_conditional_branch_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::CBranch *cbranch = new L3::CBranch();
      L3::L3_item then_dest;
      then_dest.name = parsed_strings.end()[-2];
      L3::L3_item else_dest;
      else_dest.name = parsed_strings.end()[-1];
      L3::Variable *condition = parsed_variables.at(0);
      cbranch->condition = *condition;
      cbranch->then_dest = then_dest;
      cbranch->else_dest = else_dest;
      p.functions.back()->instructions.push_back(cbranch);
      clear_memory();
    }
  };

  template<> struct action < L3_return_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::Return *ret = new L3::Return();
      p.functions.back()->instructions.push_back(ret);
      clear_memory();
    }
  };

  template<> struct action < L3_returnvalue_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::ReturnValue *ret = new L3::ReturnValue();
      L3::L3_t retvar = parsed_t_vals.back();
      ret->value = retvar;
      p.functions.back()->instructions.push_back(ret);
      clear_memory();
    }
  };

  template<> struct action < L3_call_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::Call *call = new L3::Call();
      call->callee = parsed_callee;
      call->args.insert(
          call->args.end(),
          parsed_args.begin(),
          parsed_args.end()
      );
      p.functions.back()->instructions.push_back(call);
      clear_memory();
    }
  };

  template<> struct action < L3_call_assign_rule >{
    static void apply( const pegtl::input &in, L3::Program &p){
      L3::CallAssign *calla = new L3::CallAssign();
      calla->callee = parsed_callee;
      calla->args.insert(
          calla->args.end(),
          parsed_args.begin(),
          parsed_args.end()
      );
      calla->lhs = *parsed_variables.at(0);
      p.functions.back()->instructions.push_back(calla);
      clear_memory();
    }
  };

  template<> struct action < L3_function_name_rule >{
      static void apply( const pegtl::input &in, L3::Program &p){
        L3::Function *fn = new L3::Function();
        fn->name = parsed_strings.back();
        p.functions.push_back(fn);
        clear_memory();
      }
  };


  L3::Program L3_parse_file (char *fileName){

    /*
     * Check the grammar for some possible issues.
     */
    pegtl::analyze< L3::grammar >();

    /*
     * Parse.
     */
    L3::Program p;
    pegtl::file_parser(fileName).parse< L3::grammar, L3::action >(p);

    return p;
  }
} // L3
