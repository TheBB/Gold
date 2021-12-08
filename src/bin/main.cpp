#include <iostream>
#include <memory>
#include <vector>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


// Object mkfunc(int l) {
//     auto eval = [l](EvaluationContext& ctx, const std::vector<Object>& args) {
//         return Object::integer(l);
//     };
//     return Object::closure(eval);
// }


int main(int argc, char **argv) {
    // auto func = mkfunc(3);
    // EvaluationContext ctx;
    // std::vector<Object> args;
    // auto retval = func(ctx, args);
    // std::cout << retval << std::endl;

    // std::string code("let sum = (x,y) => x + y\nsum(1,2)");
    // std::string code("let double = (x) => x + x\nlet applytwice = (f,x) => f(f(x))\napplytwice(double, [1])");
    std::string code("truet");
    auto value = evaluate_string(code);
    // debug_parse(code, false);
    // debug_parse_tree(code, false);
    // auto node = parse(code, false);
    // std::cout << *node << std::endl;

    // auto object = node->evaluate();

    std::cout << value << std::endl;

    // // Namespace ns;
    // // ns["hi"] = Object::integer(1);
    // // ns["bob"] = Object::integer(2);

    // auto myfunc = [](EvaluationContext& ctx, const std::vector<Object>& args) {
    //     return Object::integer(1);
    // };

    // auto myclosure = Object::closure(myfunc);

    // EvaluationContext ctx;
    // std::vector<Object> args;
    // auto retval = myclosure(ctx, args);
    // std::cout << retval << std::endl;

    // return 1;
}
