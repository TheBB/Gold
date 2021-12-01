#include <iostream>
#include <math.h>

#include "gold.hpp"

using namespace Gold;


int main(int argc, char **argv) {
    debug_parse("0");
    auto obj = parse("0")->object();
    std::cout << obj << std::endl;
}
