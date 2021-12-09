#include <iostream>
#include <memory>
#include <vector>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


int main(int argc, char **argv) {
    try {
        std::string code("() => a");
        auto value = evaluate_string(code);
        std::cout << value << std::endl;
    }
    catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
    }

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
