#include <iostream>
#include <memory>
#include <vector>

#include <fmt/core.h>
#include "json.hpp"
#include "cxxopts.hpp"

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;
using namespace nlohmann;


template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


struct TypeException: public std::exception {
    std::string reason;
    TypeException(std::string s) : reason(s) {}
    const char* what() const noexcept { return reason.c_str(); }
};


static json from_object(Object obj) {
    return std::visit(overloaded {
        [](Object::Null) { return json(nullptr); },
        [](Object::Integer x) { return json(x); },
        [](Object::String x) { return json(x); },
        [](Object::Boolean x) { return json(x); },
        [](Object::Floating x) { return json(x); },
        [](Object::Map x) {
            json r;
            for (auto& [key, value] : *x)
                r[key] = from_object(value);
            return r;
        },
        [](Object::List x) {
            json r;
            for (auto& value : *x)
                r.push_back(from_object(value));
            return r;
        },
        [&obj](auto&&) -> json {
            throw TypeException(fmt::format("not convertible to json: `{}`", obj.type_name()));
        }
    }, obj.data());
}


int main(int argc, char **argv) {
    cxxopts::Options options("gold-to-json", "Convert Gold scripts to JSON");
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

    Object value;
    try {
        if (result.count("code"))
            value = evaluate_string(result["code"].as<std::string>());
        else
            value = evaluate_file(result["file"].as<std::vector<std::string>>()[0]);
    }
    catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 2;
    }

    json j;
    try {
        j = from_object(value);
    }
    catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 3;
    }

    std::cout << j.dump(2) << std::endl;
}
