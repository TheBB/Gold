#include <iostream>
#include <math.h>

#include "gold.hpp"

using namespace Gold;

int main(int argc, char **argv) {
    auto someint = Object::integer(3);
    auto otherint = Object::integer(4);
    auto res = someint + otherint;
    auto mystr = Object::string("hi there");
    std::cout << (res.type() == Type::integer) << std::endl;
    std::cout << res << std::endl;
    std::cout << mystr << std::endl;
    std::cout << Object::boolean(true) << std::endl;
    std::cout << Object::boolean(false) << std::endl;
    std::cout << Object::floating(M_PI) << std::endl;
    std::cout << Object::floating(1.0) << std::endl;

    auto mylist = Object::list({ Object::integer(1), Object::integer(2) });
    auto seclist = Object::list({ Object::integer(3), Object::integer(4) });
    std::cout << (mylist + seclist) << std::endl;

    auto mymap = Object::map({
        std::make_pair("high", Object::integer(1)),
        std::make_pair("low", Object::integer(0))
    });
    std::cout << mymap << std::endl;
}
