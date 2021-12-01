#include <algorithm>
#include <iterator>
#include <iostream>

#include <fmt/core.h>

#include "gold.hpp"

#include "objects.hpp"

using namespace Gold;


Type Object::type() const {
    return _object->type();
}


std::string Object::type_name() const {
    switch (type()) {
    case Type::integer: return "integer";
    case Type::string: return "integer";
    case Type::boolean: return "boolean";
    case Type::floating: return "floating";
    case Type::map: return "map";
    case Type::list: return "list";
    case Type::function: return "function";
    case Type::error: return "error";
    default: return "??";
    }
}


Object Object::integer(int value) {
    return Object(std::make_shared<Integer>(value));
}


Object Object::string(const std::string& message) {
    return Object(std::make_shared<String>(message));
}


Object Object::boolean(bool value) {
    return Object(std::make_shared<Boolean>(value));
}


Object Object::floating(double value) {
    return Object(std::make_shared<Floating>(value));
}


Object Object::map(std::map<std::string, Object> elements) {
    return Object(std::make_shared<Map>(elements));
}


Object Object::list(std::vector<Object> elements) {
    return Object(std::make_shared<List>(elements));
}


Object Object::error(const std::string& message) {
    return Object(std::make_shared<Error>(message));
}


int Object::unsafe_integer() const {
    return std::static_pointer_cast<Integer>(_object)->value();
}


const std::string& Object::unsafe_string() const {
    return std::static_pointer_cast<String>(_object)->string();
}


bool Object::unsafe_boolean() const {
    return std::static_pointer_cast<Boolean>(_object)->value();
}


double Object::unsafe_floating() const {
    return std::static_pointer_cast<Floating>(_object)->value();
}


const std::map<std::string, Object>& Object::unsafe_map() const {
    return std::static_pointer_cast<Map>(_object)->map();
}


const std::vector<Object>& Object::unsafe_list() const {
    return std::static_pointer_cast<List>(_object)->list();
}


const std::string& Object::unsafe_error() const {
    return std::static_pointer_cast<Error>(_object)->message();
}


Object Object::operator+(Object other) {
    switch (type()) {
    case Type::integer:
        switch (other.type()) {
        case Type::integer:
            return Object::integer(unsafe_integer() + other.unsafe_integer());
        case Type::floating:
            return Object::floating(unsafe_integer() + other.unsafe_floating());
        default: break;
        }
        break;
    case Type::floating:
        switch (other.type()) {
        case Type::integer:
            return Object::floating(unsafe_floating() + other.unsafe_integer());
        case Type::floating:
            return Object::floating(unsafe_floating() + other.unsafe_floating());
        default: break;
        }
        break;
    case Type::string:
        if (other.type() == Type::string) {
            return Object::string(unsafe_string() + other.unsafe_string());
        }
        break;
    case Type::list:
        if (other.type() == Type::list) {
            std::vector<Object> elements;
            std::copy(unsafe_list().begin(), unsafe_list().end(), std::back_inserter(elements));
            std::copy(other.unsafe_list().begin(), other.unsafe_list().end(), std::back_inserter(elements));
            return Object::list(elements);
        }
        break;
    default: break;
    }

    return Object::error(fmt::format("no match for `{}` + `{}`", type_name(), other.type_name()));
}


Object Object::operator-(Object other) {
    switch (type()) {
    case Type::integer:
        switch (other.type()) {
        case Type::integer:
            return Object::integer(unsafe_integer() - other.unsafe_integer());
        case Type::floating:
            return Object::floating(unsafe_integer() - other.unsafe_floating());
        default: break;
        }
        break;
    case Type::floating:
        switch (other.type()) {
        case Type::integer:
            return Object::floating(unsafe_floating() - other.unsafe_integer());
        case Type::floating:
            return Object::floating(unsafe_floating() - other.unsafe_floating());
        default: break;
        }
        break;
    default: break;
    }

    return Object::error(fmt::format("no match for `{}` - `{}`", type_name(), other.type_name()));
}


std::ostream& operator<<(std::ostream& os, const Object& obj) {
    switch (obj.type()) {
    case Type::integer:
        os << obj.unsafe_integer();
        break;
    case Type::string:
        os << "\"" << obj.unsafe_string() << "\"";
        break;
    case Type::boolean:
        os << (obj.unsafe_boolean() ? "true" : "false");
        break;
    case Type::floating:
        os << fmt::format("{}", obj.unsafe_floating());
        break;
    case Type::map: {
        os << "{";
        bool first = true;
        for (auto const& it : obj.unsafe_map()) {
            if (!first)
                os << ", ";
            os << it.first << ": " << it.second;
            first = false;
        }
        os << "}";
        break;
    }
    case Type::list: {
        os << "[";
        bool first = true;
        for (auto obj : obj.unsafe_list()) {
            if (!first)
                os << ", ";
            os << obj;
            first = false;
        }
        os << "]";
        break;
    }
    default:
        os << "??";
    }
    return os;
}


// struct PackageVersion {
//     int major;
//     int minor;
//     int patch;
// };

// struct PackageConfig {
//     std::string name;
//     PackageVersion version;
//     std::vector<std::string> authors;
// };

// #include <lexy/callback.hpp>
// #include <lexy/dsl.hpp>

// namespace grammar
// {
//     namespace lexy = ::lexy;
//     namespace dsl = ::lexy::dsl;

//     struct name : lexy::token_production
// {
//     struct invalid_character
//     {
//         static constexpr auto name = "invalid name character";
//     };

//     // Match an alpha character, followed by zero or more alphanumeric characters or underscores.
//     // Captures it all into a lexeme.
//     static constexpr auto rule = [] {
//         auto lead_char     = dsl::ascii::alpha;
//         auto trailing_char = dsl::ascii::alnum / dsl::lit_c<'_'>;

//         return dsl::identifier(lead_char, trailing_char)
//                + dsl::peek(dsl::ascii::space).error<invalid_character>;
//     }();

//     // The final value of this production is a std::string we've created from the lexeme.
//     static constexpr auto value = lexy::as_string<std::string>;
// };

// struct version : lexy::token_production
// {
//     struct forbidden_build_string
//     {
//         static constexpr auto name = "build string not supported";
//     };

//     // Match three integers separated by dots, or the special tag "unreleased".
//     static constexpr auto rule = [] {
//         auto number      = dsl::try_(dsl::integer<int>(dsl::digits<>), dsl::nullopt);
//         auto dot         = dsl::try_(dsl::period, dsl::find(dsl::digit<>));
//         auto dot_version = dsl::times<3>(number, dsl::sep(dot))
//                            + dsl::peek_not(dsl::lit_c<'-'>).error<forbidden_build_string>;

//         auto unreleased = LEXY_LIT("unreleased");

//         return unreleased | dsl::else_ >> dot_version;
//     }();

//     // Construct a PackageVersion as the result of the production.
//     static constexpr auto value
//         = lexy::bind(lexy::construct<PackageVersion>, lexy::_1 or 0, lexy::_2 or 0, lexy::_3 or 0);
// };

// struct author
// {
//     struct invalid_character
//     {
//         static constexpr auto name = "invalid string character";
//     };

//     // Match zero or more non-control code points ("characters") surrounded by quotation marks.
//     // We allow `\u` and `\U` as escape sequences.
//     static constexpr auto rule = [] {
//         auto cp     = (dsl::code_point - dsl::ascii::control).error<invalid_character>;
//         auto escape = dsl::backslash_escape                                //
//                           .rule(dsl::lit_c<'u'> >> dsl::code_point_id<4>)  //
//                           .rule(dsl::lit_c<'U'> >> dsl::code_point_id<8>); //

//         return dsl::quoted(cp, escape);
//     }();

//     // Construct a UTF-8 string from the quoted content.
//     static constexpr auto value = lexy::as_string<std::string, lexy::utf8_encoding>;
// };

// struct author_list
// {
//     // Match a comma separated (non-empty) list of authors surrounded by square brackets.
//     static constexpr auto rule = dsl::square_bracketed.list(dsl::p<author>, dsl::sep(dsl::comma));

//     // Collect all authors into a std::vector.
//     static constexpr auto value = lexy::as_list<std::vector<std::string>>;
// };

// struct config
// {
//     struct unknown_field
//     {
//         static constexpr auto name = "unknown config field";
//     };
//     struct duplicate_field
//     {
//         static constexpr auto name = "duplicate config field";
//     };

//     // Whitespace is ' ' and '\t'.
//     static constexpr auto whitespace = dsl::ascii::blank;

//     static constexpr auto rule = [] {
//         auto make_field = [](auto name, auto rule) {
//             auto end = dsl::try_(dsl::newline, dsl::until(dsl::newline));
//             return name >> (dsl::try_(dsl::lit_c<'='>) + rule + end);
//         };

//         auto name_field    = make_field(LEXY_LIT("name"), LEXY_MEM(name) = dsl::p<name>);
//         auto version_field = make_field(LEXY_LIT("version"), LEXY_MEM(version) = dsl::p<version>);
//         auto authors_field
//             = make_field(LEXY_LIT("authors"), LEXY_MEM(authors) = dsl::p<author_list>);

//         auto combination = dsl::combination(name_field, version_field, authors_field)
//                                .missing_error<unknown_field>.duplicate_error<duplicate_field>;
//         return combination + dsl::whitespace(dsl::ascii::space) + dsl::eof;
//     }();

//     static constexpr auto value = lexy::as_aggregate<PackageConfig>;
// };

// }


// #include <lexy/input/file.hpp>
// #include <lexy/action/parse.hpp>
// #include <lexy_ext/report_error.hpp>

// int mymain()
// {
//     auto file = lexy::read_file<lexy::utf8_encoding>("test.cfg");
//     if (!file) return 1;

//     auto result = lexy::parse<grammar::config>(file.buffer(), lexy_ext::report_error);
//     if (!result) return 2;

//     if (result.has_value())
//     {
//         PackageConfig cfg = result.value();
//         std::cout << cfg.name << std::endl;
//         std::cout << cfg.version.major << std::endl;
//         std::cout << cfg.version.minor << std::endl;
//         std::cout << cfg.version.patch << std::endl;
//         std::cout << cfg.authors[0] << std::endl;
//         return 0;
//     }

//     return 3;
// }
