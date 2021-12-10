#include <iostream>
#include <memory>
#include <vector>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


using vt = std::variant<int, double>;
template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

int main(int argc, char **argv) {
    // std::string code("1 + 2");
    // debug_parse (code, false);
    // debug_parse_tree(code, false);

    // auto ast = parse(code, false);
    // std::cout << *ast << std::endl;

    // vt a(1);
    // vt b(2.0);

    // std::visit(overloaded {
    //     [](int& a, double& b) { std::cout << "int double" << std::endl; },
    //     [](auto&& a, auto&& b) { std::cout << "whatever" << std::endl; }
    // }, a, b);

    try {
        std::string code(argv[1]);
        auto value = evaluate_string(code);
        std::cout << value << std::endl;
    }
    catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
    }

}
