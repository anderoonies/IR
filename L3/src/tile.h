#include "tree.h"
#include <vector>
#include <iostream>
#include <list>
#include <map>
#include <algorithm>

using namespace std;


namespace tile {

    struct Tile {
      int64_t cost;
      Tile() : cost(1) {};
      ~Tile() {};
      shared_ptr<tree::Tree> tree;
      virtual int coverage(shared_ptr<tree::Tree>) { return 0; };
      virtual bool covers(shared_ptr<tree::Tree>) { return false; };
      virtual vector<string> generate_instructions(shared_ptr<tree::Tree>) { return {"implement me"}; };
      virtual vector<string> dump_instructions() { return {"implement me too!"}; };
      virtual shared_ptr<Tile> fire(shared_ptr<tree::Tree>) { return nullptr; };
      virtual vector<shared_ptr<tree::Tree>> get_subtrees() { return {nullptr}; };
    };

    struct Return : public Tile {
        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::ret) {
            return true;
          }
          return false;
        }

        shared_ptr<Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<Return> fired_tile = make_shared<Return>();
          return fired_tile;
        }

        vector<string> dump_instructions() {
          return {"(return)"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {NULL};
        };
    };

    struct ReturnValue : virtual Tile {
        L3::L3_item value;

        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::retv) {
            return true;
          }
          return false;
        }

        shared_ptr<tile::Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<ReturnValue> fired_tile = make_shared<ReturnValue>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          return {"(rax <- " + tree->lhs->root->item.name + ")",
                  "(return)"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {tree->lhs};
        };
    };

    struct Assignment : public Tile {
        L3::L3_item lhs;
        L3::L3_item rhs;

        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::assn) {
            return true;
          }
          return false;
        }

        shared_ptr<tile::Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<Assignment> fired_tile = make_shared<Assignment>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          return {"(" + tree->root->item.name + " <- " + tree->lhs->root->item.name + ")"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {tree->lhs};
        };
    };

    struct Arithmetic : public Tile {
        L3::L3_item lhs;
        L3::L3_item arith_lhs;
        L3::L3_item arith_rhs;
        string op_string;

        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::add ||
              tree->op == tree::sub ||
              tree->op == tree::mul ||
              tree->op == tree::l3and ||
              tree->op == tree::lshift ||
              tree->op == tree::rshift) {
            return true;
          }
          return false;
        }

        shared_ptr<tile::Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<Arithmetic> fired_tile = make_shared<Arithmetic>();
          fired_tile->tree = tree;
          switch (tree->op) {
            case tree::add:
              op_string = "+=";
              break;
            case tree::mul:
              op_string = "*=";
              break;
            case tree::sub:
              op_string = "-=";
              break;
            case tree::l3and:
              op_string = "&=";
              break;
            case tree::lshift:
              op_string = "<<=";
              break;
            case tree::rshift:
              op_string = ">>=";
              break;
            default:
              op_string = "your code sucks";
              break;
          };
          fired_tile->op_string = op_string;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          return {"(" + tree->root->item.name + " <- " + tree->lhs->root->item.name + ")",
                  "(" + tree->root->item.name + " " + op_string + " " + tree->rhs->root->item.name + ")"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {tree->lhs, tree->rhs};
        };
    };

    struct Comparison : public Tile {
        L3::L3_item lhs;
        L3::L3_item comp_lhs;
        L3::L3_item comp_rhs;
        string op_string;

        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::lt ||
              tree->op == tree::lte ||
              tree->op == tree::eq) {
            return true;
          }
          return false;
        }

        shared_ptr<tile::Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<Comparison> fired_tile = make_shared<Comparison>();
          fired_tile->tree = tree;
          switch (tree->op) {
            case tree::lt:
              op_string = "<";
              break;
            case tree::lte:
              op_string = "<=";
              break;
            case tree::eq:
              op_string = "=";
              break;
            default:
              op_string = "your code sucks";
              break;
          };
          fired_tile->op_string = op_string;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          return {"(" + tree->root->item.name + " <- " +
                  tree->lhs->root->item.name + " " +
                  op_string + " " +
                  tree->rhs->root->item.name + ")"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {tree->lhs, tree->rhs};
        };
    };

    struct Branch : public Tile {
        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::branch) {
            return true;
          }
          return false;
        }

        shared_ptr<Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<Branch> fired_tile = make_shared<Branch>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          return {"(goto " + tree->root->item.name + ")"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {NULL};
        };
    };

    struct ConditionalBranch : public Tile {
        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::cbranch) {
            return true;
          }
          return false;
        }

        shared_ptr<Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<ConditionalBranch> fired_tile = make_shared<ConditionalBranch>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          return {"(cjump " + tree->root->item.name + " = 1 " + tree->data.at(0).name + " " + tree->data.at(1).name + ")"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {NULL};
        };
    };

    struct Label : virtual Tile {
        L3::L3_item value;

        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::label) {
            return true;
          }
          return false;
        }

        shared_ptr<tile::Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<Label> fired_tile = make_shared<Label>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          return {":" + tree->data.at(0).name};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {NULL};
        };
    };

    struct Call : public Tile {
        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::call) {
            return true;
          }
          return false;
        }

        shared_ptr<Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<Call> fired_tile = make_shared<Call>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          string n_args;
          string callee = tree->data.at(0).name;
          bool runtime = true;
          if (callee == "print")
            n_args = "1";
          else if (callee == "allocate")
            n_args = "2";
          else if (callee == "array-error")
            n_args = "0";
          else {
            n_args = tree->data.at(1).name;
            runtime = false;
          }
          if (!runtime) {
            string ret_label;
            ret_label = tree->data.at(0).name;
            ret_label.erase(ret_label.begin());
            ret_label = ":l3ret" + to_string(rand() % 100) + ret_label;
            return {"((mem rsp -8) <- " + ret_label + ")",
                    "(call " + tree->data.at(0).name + " " + n_args + ")",
                    ret_label};
          } else {
            return {"(call " + tree->data.at(0).name + " " + n_args + ")"};
          }
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {NULL};
        };
    };

    struct CallAssign : virtual Tile {
        L3::L3_item value;

        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::callassign) {
            return true;
          }
          return false;
        }

        shared_ptr<tile::Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<CallAssign> fired_tile = make_shared<CallAssign>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          string n_args;
          string callee = tree->data.at(0).name;
          bool runtime = true;
          if (callee == "print")
            n_args = "1";
          else if (callee == "allocate")
            n_args = "2";
          else if (callee == "array-error")
            n_args = "0";
          else {
            n_args = tree->data.at(1).name;
            runtime = false;
          }
          if (!runtime) {
            string ret_label;
            ret_label = tree->data.at(0).name;
            ret_label.erase(ret_label.begin());
            ret_label = ":l3ret" + to_string(rand() % 100) + ret_label;
            return {"((mem rsp -8) <- " + ret_label + ")",
                    "(call " + tree->data.at(0).name + " " + n_args + ")",
                    ret_label,
                    "(" + tree->root->item.name + " <- rax)"};
          } else {
            return {"(call " + tree->data.at(0).name + " " + n_args + ")",
                    "(" + tree->root->item.name + " <- rax)"};
          }
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {tree->lhs};
        };
    };

    struct Load : virtual Tile {
        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::load) {
            return true;
          }
          return false;
        }

        shared_ptr<tile::Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<Load> fired_tile = make_shared<Load>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          string n_args;
          return {"(" + tree->root->item.name + " <- (mem " + tree->lhs->root->item.name + " 0))"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {tree->lhs};
        };
    };

    struct Store : virtual Tile {
        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::store) {
            return true;
          }
          return false;
        }

        shared_ptr<tile::Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<Store> fired_tile = make_shared<Store>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          string n_args;
          return {"((mem " + tree->root->item.name + " 0) <- " + tree->lhs->root->item.name + ")"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {tree->lhs};
        };
    };

    struct Inc : virtual Tile {
        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops + 1;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::add &&
              tree->root->item.name == tree->lhs->root->item.name &
              tree->rhs->root->item.name == "1") {
            return true;
          }
          return false;
        }

        shared_ptr<tile::Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<Inc> fired_tile = make_shared<Inc>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          return {"(" + tree->root->item.name + "++)"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {tree->lhs, tree->rhs};
        };
    };

    struct Dec : virtual Tile {
        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops + 1;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::sub &&
              tree->root->item.name == tree->lhs->root->item.name &
              tree->rhs->root->item.name == "1") {
            return true;
          }
          return false;
        }

        shared_ptr<tile::Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<Dec> fired_tile = make_shared<Dec>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          return {"(" + tree->root->item.name + "--)"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {tree->lhs, tree->rhs};
        };
    };

    struct LoadOffset : virtual Tile {
        // this helps.
        bool is_number(const string& s) {
          return !s.empty() && find_if(s.begin(), s.end(), [](char c) { return !isdigit(c); }) == s.end();
        }
        bool valid_offset(shared_ptr<tree::Tree> tree) {
          if (tree->op != tree::add)
            return false;
          if (is_number(tree->rhs->root->item.name) &&
              stoi(tree->rhs->root->item.name) % 8 == 0)
            return true;
          return false;
        }
        int coverage(shared_ptr<tree::Tree> tree) {
          if (covers(tree)) {
            return tree->n_ops + 3;
          }
          return 0;
        }

        bool covers(shared_ptr<tree::Tree> tree) {
          if (tree->op == tree::load &&
               tree->lhs->op == tree::add &&
               valid_offset(tree->lhs)) {
            return true;
          }
          return false;
        }

        shared_ptr<tile::Tile> fire(shared_ptr<tree::Tree> tree) {
          shared_ptr<LoadOffset> fired_tile = make_shared<LoadOffset>();
          fired_tile->tree = tree;
          return fired_tile;
        }

        vector<string> dump_instructions() {
          return {"(" + tree->root->item.name + " <- (mem " + tree->lhs->lhs->root->item.name + " " + tree->lhs->rhs->root->item.name + "))"};
        }

        vector<shared_ptr<tree::Tree>> get_subtrees() {
          return {nullptr};
        };
    };
}

vector<vector<shared_ptr<tile::Tile>>> tile_forest(vector<shared_ptr<tree::Tree>> forest);
