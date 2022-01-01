#include <fstream>

#include "cxxopts.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


int main(int argc, char** argv) {
    cxxopts::Options options("gold-parsecheck", "Debug Gold parsing");
    options.add_options()
        ("h,help", "show usage")
        ("c,code", "code to evaluate", cxxopts::value<std::string>())
        ("file", "path of file to evaluate", cxxopts::value<std::vector<std::string>>());
    options.parse_positional({"file"});
    options.positional_help("[FILE]");
    auto result = options.parse(argc, argv);

    if (result.count("help")) {
        std::cout << options.help() << std::endl;
        return 0;
    }

    if (!result.count("code") && !result.count("file")) {
        std::cerr << "Missing path to file or code to evaluate" << std::endl;
        return 1;
    }
    else if (result.count("file") > 1) {
        std::cerr << "Too many arguments" << std::endl;
        return 1;
    }

    std::string code;
    if (result.count("code"))
        code = result["code"].as<std::string>();
    else {
        std::ifstream input(result["file"].as<std::vector<std::string>>()[0]);
        std::stringstream ss;
        ss << input.rdbuf();
        code = ss.str();
    }

    std::cout << code << std::endl;
    debug_parse(code);
    debug_parse_tree(code);

    return 0;
}
