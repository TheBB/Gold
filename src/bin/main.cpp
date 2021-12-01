#include <iostream>
#include <math.h>

#include "gold.hpp"

using namespace Gold;


int main(int argc, char **argv) {
    if (!analyze_grammar())
        return 1;

    std::string mystr;

    // mystr = "[   true, 1  ,   ]";
    mystr = "true";
    debug_parse(mystr);
    auto node = parse(mystr);

    if (node)
        std::cout << *node << std::endl;
    else
        std::cout << "ah" << std::endl;
}
