#include <iostream>
#include <math.h>

#include "gold.hpp"

using namespace Gold;


int main(int argc, char **argv) {
    // debug_parse("0.1");
    auto obj = parse("\"h\\\\i\"")->object();
    std::cout << obj << std::endl;
}
