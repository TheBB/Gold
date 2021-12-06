#include <iostream>
#include <memory>
#include <vector>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;
using namespace Gold::Ast;


int main(int argc, char **argv) {
    // std::string code("a(1, 2)");
    std::string code("((x,y) => x + y)(1, 2)");
    debug_parse(code);
    debug_parse_tree(code);
    auto node = parse(code);
    std::cout << *node << std::endl;
}
