#include "tile.h"
#include <iostream>
#include <vector>

using namespace std;

vector<shared_ptr<tile::Tile>> tile_shelf = {make_shared<tile::Return>(), make_shared<tile::ReturnValue>(),
                                             make_shared<tile::Assignment>(), make_shared<tile::Arithmetic>(),
                                             make_shared<tile::Comparison>(), make_shared<tile::Branch>(),
                                             make_shared<tile::ConditionalBranch>(), make_shared<tile::Call>(),
                                             make_shared<tile::CallAssign>(),
                                             make_shared<tile::Inc>(), make_shared<tile::Dec>(),
                                             make_shared<tile::Load>(), make_shared<tile::Store>(),
                                             make_shared<tile::LoadOffset>(),
                                             make_shared<tile::Label>()};

vector<shared_ptr<tile::Tile>> tile_tree(shared_ptr<tree::Tree> tree) {
  if (tree == nullptr || tree->op == tree::null_op)
    return {nullptr};

  shared_ptr<vector<shared_ptr<tile::Tile>>> tiling = make_shared<vector<shared_ptr<tile::Tile>>>();
  shared_ptr<tile::Tile> candidate;
  int candidate_coverage = -1;
  for (auto tile : tile_shelf) {
    if (tile->covers(tree)) {
      if (tile->coverage(tree) > candidate_coverage) {
        candidate = tile;
        candidate_coverage = tile->coverage(tree);
      }
    }
  }
  shared_ptr<tile::Tile> covering_tile = candidate->fire(tree);
  tiling->push_back(covering_tile);

  for (auto subt : covering_tile->get_subtrees()) {
    vector<shared_ptr<tile::Tile>> subtiling = tile_tree(subt);
    for (auto tile : subtiling)
      if (!(tile == nullptr)) tiling->push_back(tile);
  }

  return *tiling;
}

vector<vector<shared_ptr<tile::Tile>>> tile_forest(vector<shared_ptr<tree::Tree>> forest) {
  vector<vector<shared_ptr<tile::Tile>>> tiling;
  for (auto tree : forest) {
    tiling.push_back(tile_tree(tree));
  }
  return tiling;
}
