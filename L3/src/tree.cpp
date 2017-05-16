#include "tree.h"
#include <iostream>

using namespace std;

shared_ptr<tree::Tree> generate_tree(L3::Instruction *i, string fun_id){
  shared_ptr<tree::Tree> instruction_tree(new tree::Tree());
  if (L3::Assignment *assn = dynamic_cast<L3::Assignment *>(i))
  {
    instruction_tree->root = make_shared<tree::Tree>();
    instruction_tree->root->item = assn->lhs;
    instruction_tree->lhs = make_shared<tree::Tree>();
    instruction_tree->lhs->root = make_shared<tree::Tree>();
    instruction_tree->lhs->root->item = assn->rhs;
    instruction_tree->op = tree::assn;
    instruction_tree->n_ops = 2;
  } else if (L3::Arithmetic *arith = dynamic_cast<L3::Arithmetic *>(i))
  {
    instruction_tree->root = make_shared<tree::Tree>();
    instruction_tree->root->item = arith->lhs;
    instruction_tree->lhs = make_shared<tree::Tree>();
    instruction_tree->lhs->root = make_shared<tree::Tree>();
    instruction_tree->lhs->root->item = arith->arith_lhs;
    instruction_tree->rhs = make_shared<tree::Tree>();
    instruction_tree->rhs->root = make_shared<tree::Tree>();
    instruction_tree->rhs->root->item = arith->arith_rhs;
    instruction_tree->n_ops = 3;
    switch(arith->arith_op) {
      case L3::plus:
        instruction_tree->op = tree::add;
        break;
      case L3::minus:
        instruction_tree->op = tree::sub;
        break;
      case L3::times:
        instruction_tree->op = tree::mul;
        break;
      case L3::l3and:
        instruction_tree->op = tree::l3and;
        break;
      case L3::lshift:
        instruction_tree->op = tree::lshift;
        break;
      case L3::rshift:
        instruction_tree->op = tree::rshift;
        break;
    }
  } else if (L3::Comparison *comp = dynamic_cast<L3::Comparison *>(i))
  {
    instruction_tree->root = make_shared<tree::Tree>();
    instruction_tree->root->item = comp->lhs;
    instruction_tree->lhs = make_shared<tree::Tree>();
    instruction_tree->lhs->root = make_shared<tree::Tree>();
    instruction_tree->lhs->root->item = comp->comp_lhs;
    instruction_tree->rhs = make_shared<tree::Tree>();
    instruction_tree->rhs->root = make_shared<tree::Tree>();
    instruction_tree->rhs->root->item = comp->comp_rhs;
    instruction_tree->n_ops = 3;
    switch(comp->comp_op)  {
      case L3::lt:
        instruction_tree->op = tree::lt;
        break;
      case L3::lte:
        instruction_tree->op = tree::lte;
        break;
      case L3::eq:
        instruction_tree->op = tree::eq;
        break;
      case L3::gt:
        // switch the operators
        instruction_tree->op = tree::lt;
        instruction_tree->lhs->root->item = comp->comp_rhs;
        instruction_tree->rhs->root->item = comp->comp_lhs;
        break;
      case L3::gte:
        instruction_tree->op = tree::lte;
        instruction_tree->lhs->root->item = comp->comp_rhs;
        instruction_tree->rhs->root->item = comp->comp_lhs;
        break;
    }
  } else if (L3::Load *load = dynamic_cast<L3::Load *>(i))
  {
    instruction_tree->root = make_shared<tree::Tree>();
    instruction_tree->root->item = load->lhs;
    instruction_tree->lhs = make_shared<tree::Tree>();
    instruction_tree->lhs->root = make_shared<tree::Tree>();
    instruction_tree->lhs->root->item = load->rhs;
    instruction_tree->op = tree::load;
    instruction_tree->n_ops = 2;
  } else if (L3::Store *store = dynamic_cast<L3::Store *>(i))
  {
    instruction_tree->root = make_shared<tree::Tree>();
    instruction_tree->root->item = store->lhs;
    instruction_tree->lhs = make_shared<tree::Tree>();
    instruction_tree->lhs->root = make_shared<tree::Tree>();
    instruction_tree->lhs->root->item = store->rhs;
    instruction_tree->op = tree::store;
    instruction_tree->n_ops = 2;
  } else if (L3::Branch *branch= dynamic_cast<L3::Branch *>(i))
  {
    instruction_tree->root = make_shared<tree::Tree>();
    instruction_tree->root->item = branch->dest;
    instruction_tree->root->item.name = instruction_tree->root->item.name + fun_id;
    instruction_tree->op = tree::branch;
    instruction_tree->n_ops = 1;
  } else if (L3::Label *label = dynamic_cast<L3::Label *>(i))
  {
    instruction_tree->op = tree::label;
    label->label.name = label->label.name + fun_id;
    instruction_tree->data = {label->label};
    instruction_tree->n_ops = 1;
  } else if (L3::CBranch *cbranch = dynamic_cast<L3::CBranch *>(i))
  {
    instruction_tree->root = make_shared<tree::Tree>();
    instruction_tree->root->item = cbranch->condition;
    instruction_tree->op = tree::cbranch;
    cbranch->then_dest.name = cbranch->then_dest.name + fun_id;
    cbranch->else_dest.name = cbranch->else_dest.name + fun_id;
    instruction_tree->data = {cbranch->then_dest, cbranch->else_dest};
    instruction_tree->n_ops = 3;
  } else if (L3::Return *ret = dynamic_cast<L3::Return *>(i))
  {
    instruction_tree->op = tree::ret;
    instruction_tree->n_ops = 0;
  } else if (L3::ReturnValue *retv = dynamic_cast<L3::ReturnValue *>(i))
  {
    instruction_tree->lhs = make_shared<tree::Tree>();
    instruction_tree->lhs->root = make_shared<tree::Tree>();
    instruction_tree->lhs->root->item = retv->value;
    instruction_tree->op = tree::retv;
    instruction_tree->n_ops = 1;
  } else if (L3::CallAssign *calla= dynamic_cast<L3::CallAssign *>(i))
  {
    instruction_tree->root = make_shared<tree::Tree>();
    instruction_tree->root->item = calla->lhs;
    instruction_tree->op = tree::callassign;
    instruction_tree->data.push_back(calla->callee);
    L3::L3_item arg_size_bucket;
    arg_size_bucket.name = to_string(calla->args.size());
    instruction_tree->data.push_back(arg_size_bucket);
    instruction_tree->n_ops = 1;
  } else if (L3::Call *call= dynamic_cast<L3::Call *>(i))
  {
    instruction_tree->op = tree::call;
    instruction_tree->data.push_back(call->callee);
    L3::L3_item arg_size_bucket;
    arg_size_bucket.name = to_string(call->args.size());
    instruction_tree->data.push_back(arg_size_bucket);
    instruction_tree->n_ops = 0;
  } else {
    cerr << "Abort! this shouldn't be happening.\n";
  }
  return instruction_tree;
};

vector<shared_ptr<tree::Tree>> generate_forest(L3::Function f, string fun_id){
  vector<shared_ptr<tree::Tree>> trees;
  for (auto i : f.instructions) {
    shared_ptr<tree::Tree> instruction_tree = generate_tree(i, fun_id);
    trees.push_back(instruction_tree);
  }
  return trees;
}

shared_ptr<tree::Tree> merge_trees(shared_ptr<tree::Tree> tree1, shared_ptr<tree::Tree> tree2) {
  if (!(tree1->root == nullptr || tree2->lhs == nullptr) &&
      (*tree1->root == *tree2->lhs->root)) {
    tree2->lhs = tree1;
    return tree2;
  }
  if (!(tree1->root == nullptr || tree2->rhs == nullptr) &&
      (*tree1->root == *tree2->rhs->root)) {
    tree2->rhs = tree1;
    return tree2;
  }
  if (!(tree1->lhs == nullptr || tree2->root == nullptr) &&
      (*tree1->lhs->root == *tree2->root))
  {
    tree1->lhs = tree2;
    return tree1;
  }
  if (!(tree1->rhs == nullptr || tree2->root == nullptr) &&
      (*tree1->rhs->root == *tree2->root)) {
    tree1->rhs = tree2;
    return tree1;
  }
  return tree1;
}

vector<shared_ptr<tree::Tree>> merge_forest(vector<shared_ptr<tree::Tree>> trees) {
  // merges as many trees as possible
  bool finished = false;
  vector<shared_ptr<tree::Tree>> merged_trees;
  if (trees.size() > 1) {
    for (int i = trees.size() - 1; i >= 0; i--) {
      // iterate over the trees backwards, merging by pair
      if (i > 0)
        if (trees[i]->sharesNode(trees[i - 1])) {
          shared_ptr<tree::Tree> merged_tree = merge_trees(trees[i], trees[i - 1]);
          merged_trees.insert(merged_trees.begin(), merged_tree);
          i--;
        } else {
          merged_trees.insert(merged_trees.begin(), trees[i]);
        }
      else
        merged_trees.insert(merged_trees.begin(), trees[i]);
    }

    return merged_trees;
  } else {
    return trees;
  }
}
