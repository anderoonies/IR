#include "L3.h"
#include <vector>
#include <iostream>
#include <memory>

using namespace std;

namespace tree {
    enum Operator {
        null_op,
        assn, add, mul, sub, l3and,
        load, store, lshift, rshift,
        lt, lte, eq, branch, cbranch,
        ret, retv, call, callassign,
        label
    };

    struct Tree {
      L3::L3_item item;
      shared_ptr<Tree> root = nullptr;
      shared_ptr<Tree> lhs = nullptr;
      shared_ptr<Tree> rhs = nullptr;
      Operator op = null_op;
      int64_t n_ops = 2;
      vector<L3::L3_item> data;
      vector<L3::Instruction *> instructions;

      bool sharesNode(shared_ptr<Tree> other_tree) {
        if (!(root == nullptr || other_tree->lhs == nullptr) &&
                (*root == *other_tree->lhs->root))
          return true;
        if (!(root == nullptr || other_tree->rhs == nullptr) &&
            (*root == *other_tree->rhs->root))
          return true;
        if (!(lhs == nullptr || other_tree->root == nullptr) &&
            (*lhs->root == *other_tree->root))
          return true;
        if (!(rhs == nullptr || other_tree->root == nullptr) &&
            (*rhs->root == *other_tree->root))
          return true;
        return false;
      };

      bool operator==(Tree &other) {
        return item.name == other.item.name;
      }

      Tree() {

      }
    };

}

vector<shared_ptr<tree::Tree>> generate_forest(L3::Function f, string fun_id);

vector<shared_ptr<tree::Tree>> merge_forest(vector<shared_ptr<tree::Tree>> trees);
