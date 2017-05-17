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

#include "IR.h"
#include "../../lib/PEGTL/pegtl.hh"
#include "../../lib/PEGTL/pegtl/analyze.hh"

using namespace pegtl;
using namespace std;

namespace IR {

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

  struct IR_arrow_rule :
    pegtl::seq<
      seps,
      pegtl::one< '<' >,
      pegtl::one< '-' >,
      seps
    > {};

  struct IR_char_sequence_rule :
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

  struct IR_var_rule :
    pegtl::seq<
      pegtl::one< '%' >,
      IR_char_sequence_rule
    > {};

  struct IR_label_rule :
    pegtl::seq<
      pegtl::one< ':' >,
      IR_char_sequence_rule
    > {};

  struct IR_op_rule :
    pegtl::sor<
      pegtl::string< '<', '<' >,
      pegtl::string< '>', '>' >,
      pegtl::string< '<' >,
      pegtl::string< '<', '=' >,
      pegtl::string< '=' >,
      pegtl::string< '>', '=' >,
      pegtl::string< '>' >,
      pegtl::string< '+' >,
      pegtl::string< '-' >,
      pegtl::string< '*' >,
      pegtl::string< '&' >
    > {};

  struct IR_t_rule :
    pegtl::sor<
      IR_var_rule,
      number
    > {};

  struct IR_s_rule :
    pegtl::sor<
      IR_t_rule,
      IR_label_rule
    > {};

  struct IR_u_rule :
    pegtl::sor<
      IR_var_rule,
      IR_label_rule
    > {};

  struct IR_vars_rule :
    pegtl::sor<
      pegtl::seq<
        IR_t_rule,
        pegtl::star<
          pegtl::one< ',' >,
          seps,
          IR_t_rule
        >
      >,
      IR_t_rule,
      seps
    > {};

  struct IR_args_rule :
    pegtl::sor<
      pegtl::seq<
        IR_t_rule,
        pegtl::star<
          pegtl::one< ',' >,
          seps,
          IR_t_rule
        >
      >,
      IR_t_rule,
      seps
    > {};

  struct IR_callee_rule :
    pegtl::sor<
      IR_u_rule,
      pegtl::string< 'p','r','i','n','t' >,
      pegtl::string< 'a','r','r','a','y','-','e','r','r','o','r' >
    > {};

  struct IR_brackets_rule :
    pegtl::seq<
      pegtl::star<
        pegtl::string< '[',']'>
      >
    > {};

  struct IR_type_rule :
    pegtl::sor<
      pegtl::seq<
        pegtl::string< 'i','n','t','6','4' >,
        IR_brackets_rule
      >,
      pegtl::string< 't','u','p','l','e' >,
      pegtl::string< 'c','o','d','e' >
    > {};

  struct IR_T_rule :
    pegtl::sor<
      IR_type_rule,
      pegtl::string< 'v','o','i','d' >
    > {};

  struct IR_declaration_rule :
    pegtl::seq<
      seps,
      IR_type_rule,
      seps,
      IR_var_rule,
      seps
    > {};

  struct IR_declarations_rule :
    pegtl::sor<
      pegtl::seq<
        IR_declaration_rule,
        pegtl::star<
          pegtl::one< ',' >,
          seps,
          IR_declaration_rule
        >
      >,
      IR_declaration_rule,
      seps
    > {};

  struct IR_declaration_instruction_rule :
    pegtl::seq<
      seps,
      IR_declaration_rule,
      seps
    > {};

  struct IR_assignment_rule :
    pegtl::seq<
      seps,
      IR_var_rule,
      seps,
      IR_arrow_rule,
      seps,
      IR_s_rule,
      seps
    > {};

  struct IR_operation_rule :
    pegtl::seq<
      seps,
      IR_var_rule,
      seps,
      IR_arrow_rule,
      seps,
      IR_t_rule,
      seps,
      IR_op_rule,
      seps,
      IR_t_rule,
      seps
    > {};

  struct IR_indices_rule :
    pegtl::plus<
      seps,
      pegtl::one< '[' >,
      IR_t_rule,
      pegtl::one< ']' >,
      seps
    > {};

  struct IR_array_read_rule :
    pegtl::seq<
      seps,
      IR_var_rule,
      seps,
      IR_arrow_rule,
      seps,
      IR_var_rule,
      seps,
      IR_indices_rule,
      seps
    > {};

  struct IR_array_write_rule :
    pegtl::seq<
      seps,
      IR_var_rule,
      seps,
      IR_indices_rule,
      seps,
      IR_arrow_rule,
      seps,
      IR_s_rule,
      seps
    > {};

  struct IR_length_read_rule :
    pegtl::seq<
      seps,
      IR_var_rule,
      seps,
      IR_arrow_rule,
      seps, 
      pegtl::string< 'l','e','n','g','t','h' >,
      seps,
      IR_var_rule,
      seps,
      IR_t_rule,
      seps
    > {};

  struct IR_branch_rule :
    pegtl::seq<
      seps,
      pegtl::string< 'b','r' >,
      seps,
      IR_label_rule,
      seps
    > {};

  struct IR_i_label_rule:
    pegtl::seq<
      seps,
      IR_label_rule,
      seps
    > {};

  struct IR_conditional_branch_rule :
    pegtl::seq<
      seps,
      pegtl::string< 'b','r' >,
      seps,
      IR_var_rule,
      seps,
      IR_label_rule,
      seps,
      IR_label_rule,
      seps
    > {};

  struct IR_return_rule :
    pegtl::seq<
      seps,
      pegtl::string< 'r','e','t','u','r','n' >,
      seps
    > {};

  struct IR_returnvalue_rule :
    pegtl::seq<
      seps,
      pegtl::string< 'r','e','t','u','r','n' >,
      seps,
      IR_t_rule,
      seps
    > {};

  struct IR_call_rule :
    pegtl::seq<
      seps,
      pegtl::string< 'c','a','l','l' >,
      seps,
      IR_callee_rule,
      seps,
      pegtl::one< '(' >,
      seps,
      IR_args_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct IR_call_assign_rule :
    pegtl::seq<
      seps,
      IR_var_rule,
      seps,
      IR_arrow_rule,
      seps,
      pegtl::string< 'c','a','l','l' >,
      seps,
      IR_callee_rule,
      seps,
      pegtl::one< '(' >,
      seps,
      IR_args_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct IR_array_allocate_rule :
    pegtl::seq<
      seps,
      IR_var_rule,
      seps,
      IR_arrow_rule,
      seps,
      pegtl::string< 'n','e','w' >,
      seps,
      pegtl::string< 'A','r','r','a','y','(' >,
      seps,
      IR_args_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct IR_tuple_allocate_rule :
    pegtl::seq<
      seps,
      IR_var_rule,
      seps,
      IR_arrow_rule,
      seps,
      pegtl::string< 'n','e','w' >,
      seps,
      pegtl::string< 'T','u','p','l','e','(' >,
      seps,
      IR_t_rule,
      seps,
      pegtl::one< ')' >,
      seps
    > {};

  struct IR_te_rule :
    pegtl::sor<
      IR_branch_rule,
      IR_conditional_branch_rule,
      IR_returnvalue_rule,
      IR_return_rule
    > {};

  struct IR_instruction_rule :
    pegtl::sor<
      IR_array_read_rule,
      IR_array_write_rule,
      IR_length_read_rule,
      IR_array_allocate_rule,
      IR_tuple_allocate_rule,
      IR_operation_rule,
      IR_i_label_rule,
      IR_declaration_instruction_rule,
      IR_assignment_rule,
      IR_call_rule,
      IR_call_assign_rule
    > {};

  struct IR_instructions_rule :
    pegtl::star<
      seps,
      IR_instruction_rule,
      seps
    > {};

  struct IR_function_name_rule :
    pegtl::seq<
      seps,
      IR_label_rule,
      seps
    > {};

  struct IR_e_rule :
    pegtl::seq<
      seps,
      IR_label_rule,
      seps
    > {};

  struct IR_basic_block_rule :
    pegtl::seq<
      seps,
      IR_e_rule,
      seps,
      IR_instructions_rule,
      seps,
      IR_te_rule,
      seps
    > {};

  struct IR_basic_blocks_rule :
    pegtl::plus<
      IR_basic_block_rule
    > {};

  struct IR_function_rule :
    pegtl::seq<
      pegtl::string< 'd','e','f','i','n','e' >,
      seps,
      IR_T_rule,
      seps,
      IR_function_name_rule,
      seps,
      pegtl::one< '(' >,
      seps,
      IR_declarations_rule,
      seps,
      pegtl::one< ')' >,
      seps,
      pegtl::one< '{' >,
      seps,
      IR_basic_blocks_rule,
      seps,
      pegtl::one< '}' >,
      seps
    > {};

  struct IR_program_rule :
    pegtl::star<
      IR_function_rule
    > {};

  struct entry_point_rule :
    IR_program_rule {};

  struct grammar :
    pegtl::must<
      entry_point_rule
    > {};

  /////////////
  //   DATA  //
  /////////////
  
  vector<IR::Function *> parsed_functions;
  vector<shared_ptr<IR::Variable>> parsed_variables;
  vector<IR::IR_s> parsed_s_vals;
  vector<IR::IR_t> parsed_t_vals;
  vector<IR::IR_t> parsed_indices;
  vector<IR::IR_u> parsed_u_vals;
  vector<IR::IR_t> parsed_args;
  vector<IR::Variable> parsed_vars;
  vector<shared_ptr<IR::Declaration>> parsed_declarations;
  IR_callee parsed_callee;
  vector<std::string> parsed_strings;
  vector<std::string> parsed_labels;
  vector<std::string> parsed_char_seqs;
  int64_t parsed_array_declaration_dimension = -1;
  Operator parsed_op;
  Type parsed_type;
  IR_item parsed_T;
  shared_ptr<BasicBlock> parsed_basic_block;

  /////////////
  // ACTIONS //
  /////////////
  
  void add_instruction(IR::Program &p, shared_ptr<IR::Instruction> i) {
    parsed_basic_block->instructions.push_back(i);
  };

  void end_block(IR::Program &p) {
    p.functions.back()->blocks.push_back(parsed_basic_block);
  };
  
  void clear_memory() {
    parsed_variables.clear();
    parsed_s_vals.clear();
    parsed_t_vals.clear();
    parsed_u_vals.clear();
    parsed_strings.clear();
    parsed_args.clear();
    parsed_indices.clear();
    parsed_array_declaration_dimension = -1;
    parsed_declarations.clear();
  }
  
  template< typename Rule >
    struct action : pegtl::nothing< Rule > {};
  
  template<> struct action < IR_char_sequence_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      parsed_char_seqs.push_back(in.string()); 
    }
  };

  template<> struct action < IR_label_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      parsed_labels.push_back(in.string()); 
    }
  };

  template<> struct action < IR_var_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::Variable> var = make_shared<IR::Variable>();
      var->name = parsed_char_seqs.back();
      parsed_variables.push_back(var);
    }
  };

  template<> struct action < IR_op_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      std::string op = in.string();
      std::string plus ("+");
      std::string minus ("-");
      std::string times ("*");
      std::string l3and ("&");
      std::string lshift ("<<");
      std::string rshift (">>");
      std::string lt ("<");
      std::string lte ("<=");
      std::string eq ("=");
      std::string gte (">=");
      std::string gt (">");
      if (op.compare(plus) == 0)
        parsed_op = IR::plus;
      else if (op.compare(minus) == 0)
        parsed_op = IR::minus;
      else if (op.compare(times) == 0)
        parsed_op = IR::times;
      else if (op.compare(l3and) == 0)
        parsed_op = IR::l3and;
      else if (op.compare(lshift) == 0)
        parsed_op = IR::lshift;
      else if (op.compare(rshift) == 0)
        parsed_op = IR::rshift;
      else if (op.compare(lt) == 0)
        parsed_op = IR::lt;
      else if (op.compare(lte) == 0)
        parsed_op = IR::lte;
      else if (op.compare(eq) == 0)
        parsed_op = IR::eq;
      else if (op.compare(gte) == 0)
        parsed_op = IR::gte;
      else if (op.compare(gt) == 0)
        parsed_op = IR::gt;
    }
  };

  template<> struct action < IR_u_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      IR::IR_u u;
      u.name = in.string();
      if (u.name[0] == '%')
        u.name.erase(0,1);
      parsed_u_vals.push_back(u);
    }
  };

  template<> struct action < IR_t_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      IR::IR_t t;
      t.name = in.string();
      if (t.name.at(0) == '%')
        t.name.erase(0,1);
      parsed_t_vals.push_back(t);
    }
  };

  template<> struct action < IR_s_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      IR::IR_s s;
      s.name = in.string();
      if (s.name[0] == '%')
        s.name.erase(0,1);
      parsed_s_vals.push_back(s);
    }
  };

  template<> struct action < IR_args_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      // args are a property of a function call.
      parsed_args.insert(
          parsed_args.end(),
          parsed_t_vals.begin(),
          parsed_t_vals.end()
      );
    }
  };

  template<> struct action < IR_vars_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      // vars are a property of a function itself.
      // TODO

      //clear_memory();
    }
  };

  template<> struct action < IR_callee_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      IR::IR_callee callee;
      callee.name = in.string();
      parsed_callee = callee;
    }
  };

  template<> struct action < IR_T_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      parsed_T.name = in.string();
    }
  };

  template<> struct action < IR_brackets_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      parsed_array_declaration_dimension = in.string().size() / 2;
    }
  };

  template<> struct action < IR_type_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      std::string type = in.string();
      std::string int_type = "int64";
      std::string tuple_type = "tuple";
      std::string code_type = "code";
      if (int_type.compare(type.substr(0, 5)) == 0) {
        if (parsed_array_declaration_dimension > 0) {
          parsed_type.dec_type = IR::array;
          parsed_type.array_dim = parsed_array_declaration_dimension;
        } else {
          parsed_type.dec_type = IR::integer;
        }
      } else if (tuple_type.compare(type) == 0) {
        parsed_type.dec_type = IR::tuple;
      } else if (code_type.compare(type) == 0) {
        parsed_type.dec_type = IR::code;
      }
    }
  };

  template<> struct action < IR_declaration_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::Declaration> dec = make_shared<IR::Declaration>();
      dec->type = parsed_type;
      dec->var = *parsed_variables.back();
      parsed_declarations.push_back(dec);
    }
  };

  template<> struct action < IR_declarations_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      p.functions.back()->vars.insert(
        p.functions.back()->vars.end(),
        parsed_declarations.begin(),
        parsed_declarations.end()
      );
      clear_memory();
    }
  };
  
  template<> struct action < IR_declaration_instruction_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::Declaration> dec = make_shared<IR::Declaration>();
      dec->type = parsed_type;
      dec->var = *parsed_variables.at(0);
      add_instruction(p, dec);
      clear_memory();
    }
  };

  template<> struct action < IR_assignment_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      IR::Variable lhs = *parsed_variables.at(0);
      IR::IR_s rhs = parsed_s_vals.back();
      shared_ptr<IR::Assignment> assignment = make_shared<IR::Assignment>();
      assignment->lhs = lhs;
      assignment->rhs = rhs;
      add_instruction(p, assignment);
      clear_memory();
    }
  };

  template<> struct action < IR_operation_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      IR::Variable lhs = *parsed_variables.at(0);
      shared_ptr<IR::Operation> operation = make_shared<IR::Operation>();
      operation->lhs = lhs;
      operation->op_lhs = parsed_t_vals.end()[-2];
      operation->op_rhs = parsed_t_vals.end()[-1];
      operation->op = parsed_op;
      add_instruction(p, operation);
      clear_memory();
    }
  };

  template<> struct action < IR_branch_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::Branch> branch = make_shared<IR::Branch>();
      IR::IR_item dest;
      dest.name = parsed_labels.back();
      branch->dest = dest;
      add_instruction(p, branch);
      clear_memory();
    }
  };

  template<> struct action < IR_conditional_branch_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::CBranch> cbranch = make_shared<IR::CBranch>();
      IR::IR_item then_dest;
      then_dest.name = parsed_labels.end()[-2];
      IR::IR_item else_dest;
      else_dest.name = parsed_labels.end()[-1];
      shared_ptr<IR::Variable> condition = parsed_variables.at(0);
      cbranch->condition = *condition;
      cbranch->then_dest = then_dest;
      cbranch->else_dest = else_dest;
      add_instruction(p, cbranch);
      clear_memory();
    }
  };

  template<> struct action < IR_i_label_rule >{
      static void apply( const pegtl::input &in, IR::Program &p){
        shared_ptr<IR::Label> label = shared_ptr<IR::Label>();
        IR::IR_item lbl;
        lbl.name = parsed_variables.back()->name;
        label->label = lbl;
        add_instruction(p, label);
        clear_memory();
      }
  };

  template<> struct action < IR_e_rule >{
      static void apply( const pegtl::input &in, IR::Program &p){
        parsed_basic_block = make_shared<IR::BasicBlock>();
        IR::IR_item entry;
        entry.name = in.string();
        parsed_basic_block->entry_point = entry;
        clear_memory();
      }
  };

  template<> struct action < IR_te_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      end_block(p);
      clear_memory();
    }
  };

  template<> struct action < IR_call_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::Call> call = make_shared<IR::Call>();
      call->callee = parsed_callee;
      call->args.insert(
          call->args.end(),
          parsed_args.begin(),
          parsed_args.end()
      );
      add_instruction(p, call);
      clear_memory();
    }
  };

  template<> struct action < IR_call_assign_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::CallAssign> calla = make_shared<IR::CallAssign>();
      calla->callee = parsed_callee;
      calla->args.insert(
          calla->args.end(),
          parsed_args.begin(),
          parsed_args.end()
      );
      calla->lhs = *parsed_variables.at(0);
      add_instruction(p, calla);
      clear_memory();
    }
  };

  template<> struct action < IR_array_allocate_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::ArrayAllocate> alloc = make_shared<IR::ArrayAllocate>();
      alloc->lhs = *parsed_variables.at(0);
      alloc->dimensions.insert(
          alloc->dimensions.end(),
          parsed_args.begin(),
          parsed_args.end()
      );
      add_instruction(p, alloc);
      clear_memory();
    }
  };

  template<> struct action < IR_tuple_allocate_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::TupleAllocate> alloc = make_shared<IR::TupleAllocate>();
      alloc->lhs = *parsed_variables.at(0);
      alloc->dimension = parsed_t_vals.back();
      add_instruction(p, alloc);
      clear_memory();
    }
  };

  template<> struct action < IR_length_read_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::LengthRead> lr = make_shared<IR::LengthRead>();
      lr->lhs = *parsed_variables.at(0);
      lr->rhs = *parsed_variables.back();
      lr->index = parsed_t_vals.back();
      add_instruction(p, lr);
      clear_memory();
    }
  };

  template<> struct action < IR_indices_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      parsed_indices.insert(
        parsed_indices.end(),
        parsed_t_vals.begin(),
        parsed_t_vals.end()
      );
    }
  };

  template<> struct action < IR_array_read_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::IndexRead> read = make_shared<IR::IndexRead>();
      read->lhs = *parsed_variables.at(0);
      read->rhs = *parsed_variables.at(1);
      read->indices.insert(
        read->indices.end(),
        parsed_indices.begin(),
        parsed_indices.end()
      );
      add_instruction(p, read);
      clear_memory();
    }
  };

  template<> struct action < IR_array_write_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::IndexWrite> write = make_shared<IR::IndexWrite>();
      write->lhs = *parsed_variables.at(0);
      write->rhs = parsed_s_vals.back();
      write->indices.insert(
        write->indices.end(),
        parsed_indices.begin(),
        parsed_indices.end()
      );
      add_instruction(p, write);
      clear_memory();
    }
  };

  template<> struct action < IR_return_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::Return> ret = make_shared<IR::Return>();
      add_instruction(p, ret);
      clear_memory();
    }
  };

  template<> struct action < IR_returnvalue_rule >{
    static void apply( const pegtl::input &in, IR::Program &p){
      shared_ptr<IR::ReturnValue> ret = make_shared<IR::ReturnValue>();
      IR::IR_t retvar = parsed_t_vals.back();
      ret->value = retvar;
      add_instruction(p, ret);
      clear_memory();
    }
  };

  template<> struct action < IR_function_name_rule >{
      static void apply( const pegtl::input &in, IR::Program &p){
        shared_ptr<IR::Function> fn = make_shared<IR::Function>();
        fn->name = parsed_labels.back();
        p.functions.push_back(fn);
        clear_memory();
      }
  };


  IR::Program IR_parse_file (char *fileName){

    /*
     * Check the grammar for some possible issues.
     */
    pegtl::analyze< IR::grammar >();

    /*
     * Parse.
     */
    IR::Program p;
    pegtl::file_parser(fileName).parse< IR::grammar, IR::action >(p);

    return p;
  }
} // IR
