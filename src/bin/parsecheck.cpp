#include "cxxopts.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


int main(int argc, char** argv) {
    cxxopts::Options options("gold-to-json", "Convert Gold scripts to JSON");
    options.add_options()
        ("h,help", "show usage")
        ("code", "code to evaluate", cxxopts::value<std::vector<std::string>>());
    options.parse_positional({"code"});
    options.positional_help("CODE");
    auto result = options.parse(argc, argv);

    if (result.count("help")) {
        std::cout << options.help() << std::endl;
        return 0;
    }

    if (!result.count("code")) {
        std::cerr << "Missing code to evaluate" << std::endl;
        return 1;
    }
    else if (result.count("code") > 1) {
        std::cerr << "Too many arguments" << std::endl;
        return 1;
    }

    auto code = result["code"].as<std::vector<std::string>>()[0];
    debug_parse(code);
    debug_parse_tree(code);

    return 0;
}
