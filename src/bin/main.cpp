#include <iostream>
#include <memory>
#include <vector>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;
using namespace Gold::Ast;


int main(int argc, char **argv) {
    std::string code("let a = 1\na");
    debug_parse(code, false);
    debug_parse_tree(code, false);
    auto node = parse(code, false);
    std::cout << *node << std::endl;
}
