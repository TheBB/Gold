#include <algorithm>
#include <iterator>
#include <iostream>

#include <fmt/core.h>

#include "gold.hpp"

using namespace Gold;



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
            Object::List elements = std::make_shared<std::vector<Object>>();
            std::copy(unsafe_list()->begin(), unsafe_list()->end(), std::back_inserter(*elements));
            std::copy(other.unsafe_list()->begin(), other.unsafe_list()->end(), std::back_inserter(*elements));
            return Object::list(elements);
        }
        break;
    default: break;
    }

    return Object::error("TypeError", fmt::format("no match for `{}` + `{}`", type_name(), other.type_name()));
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

    return Object::error("TypeError", fmt::format("no match for `{}` - `{}`", type_name(), other.type_name()));
}


std::ostream& operator<<(std::ostream& os, const Object& obj) {
    switch (obj.type()) {
    case Object::Type::integer:
        os << obj.unsafe_integer();
        break;
    case Object::Type::string:
        os << "\"" << obj.unsafe_string() << "\"";
        break;
    case Object::Type::boolean:
        os << (obj.unsafe_boolean() ? "true" : "false");
        break;
    case Object::Type::floating:
        os << fmt::format("{}", obj.unsafe_floating());
        break;
    case Object::Type::map: {
        os << "{";
        bool first = true;
        for (auto const& it : *obj.unsafe_map()) {
            if (!first)
                os << ", ";
            os << it.first << ": " << it.second;
            first = false;
        }
        os << "}";
        break;
    }
    case Object::Type::list: {
        os << "[";
        bool first = true;
        for (auto obj : *obj.unsafe_list()) {
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
