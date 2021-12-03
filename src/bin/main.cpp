#include <iostream>
#include <math.h>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


int main(int argc, char **argv) {
    std::string code("1 / 2 + 3");
    debug_parse(code);
    debug_parse_tree(code);
    auto node = parse(code);
    std::cout << node << std::endl;
    // auto a = Object::list({ Object::integer(1), Object::integer(2) });
    // auto b = Object::list({ Object::integer(3), Object::integer(4) });
    // std::cout << a << std::endl;
    // std::cout << b << std::endl;
    // auto c = a + b;
    // std::cout << c << std::endl;
}
