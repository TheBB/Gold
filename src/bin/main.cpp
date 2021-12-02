#include <iostream>
#include <math.h>

#include "gold.hpp"

using namespace Gold;


int main(int argc, char **argv) {
    auto a = Object::list({ Object::integer(1), Object::integer(2) });
    auto b = Object::list({ Object::integer(3), Object::integer(4) });
    std::cout << a << std::endl;
    std::cout << b << std::endl;
    auto c = a + b;
    std::cout << c << std::endl;
}
