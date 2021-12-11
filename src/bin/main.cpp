#include <iostream>
#include <memory>
#include <vector>

#include <fmt/core.h>
#include "json.hpp"

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
    Object value;
    try {
        std::string code(argv[1]);
        value = evaluate_string(code);
    }
    catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 1;
    }

    json j;
    try {
        j = from_object(value);
    }
    catch (const std::exception& e) {
        std::cerr << "Error: " << e.what() << std::endl;
        return 2;
    }

    std::cout << j.dump(2) << std::endl;
}
