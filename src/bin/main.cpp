#include <iostream>
#include <memory>
#include <vector>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


int main(int argc, char **argv) {
    std::string code("{let a=1\nlet b=2\na+b}");
    debug_parse(code);
    debug_parse_tree(code);
    auto node = parse(code);
    std::cout << node << std::endl;
}
