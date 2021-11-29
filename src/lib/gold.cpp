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
