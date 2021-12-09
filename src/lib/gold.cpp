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
    case Type::null: return "null";
    case Type::map: return "map";
    case Type::list: return "list";
    case Type::closure: return "closure";
    }
    return "null";
}


Object Object::operator+(Object other) const {
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

    throw EvalException();
}


Object Object::operator-(Object other) const {
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

    throw EvalException();
}


Object Object::operator()(EvaluationContext& ctx, const std::vector<Object>& args) const {
    if (type() != Type::closure)
        throw EvalException();
    auto closure = unsafe_closure();

    ctx.push_namespace(closure->nonlocals);
    ctx.push_namespace();

    auto id_it = closure->parameters.begin();
    auto arg_it = args.begin();
    while (id_it != closure->parameters.end() && arg_it != args.end())
        ctx.assign(*id_it++, *arg_it++);
    Object retval = closure->expression->evaluate(ctx);

    ctx.pop_namespace(2);
    return retval;
}


Object Object::operator[](Object index) const {
    if (type() == Object::Type::list && index.type() == Object::Type::integer) {
        auto ix = index.unsafe_integer();
        if (ix < 0 || (size_t)ix >= unsafe_list()->size())
            throw EvalException();
        return (*unsafe_list())[ix];
    }

    else if (type() == Object::Type::map && index.type() == Object::Type::string) {
        auto ix = index.unsafe_string();
        auto map = unsafe_map();
        if (map->find(ix) == map->end())
            throw EvalException();
        return (*map)[ix];
    }

    throw EvalException();
}


Object Object::operator[](intmax_t index) const {
    if (type() != Object::Type::list)
        throw EvalException();
    if (index < 0 || (size_t)index >= unsafe_list()->size())
        throw EvalException();
    return (*unsafe_list())[index];
}


Object Object::operator[](std::string index) const {
    if (type() != Object::Type::map)
        throw EvalException();
    if (unsafe_map()->find(index) == unsafe_map()->end())
        throw EvalException();
    return (*unsafe_map())[index];
}


size_t Object::size() const {
    if (type() == Object::Type::list)
        return unsafe_list()->size();
    if (type() == Object::Type::map)
        return unsafe_map()->size();
    throw EvalException();
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
    case Object::Type::null:
        os << "null";
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
    case Object::Type::closure:
        os << "<closure>";
        break;
    }
    return os;
}


Object EvaluationContext::lookup(const std::string& key) {
    for (auto& ns : namespaces) {
        if (ns.find(key) == ns.end())
            continue;
        return ns[key];
    }
    throw EvalException();
}


Object EvaluationContext::lookup_object(const std::string& key, int index) {
    auto& ns = objects[objects.size() - index];
    if (ns.find(key) == ns.end())
        throw EvalException();
    return ns[key];
}


void EvaluationContext::assign(const std::string& key, Object value) {
    namespaces.front()[key] = value;
}


void EvaluationContext::assign_object(const std::string& key, Object value) {
    objects.back()[key] = value;
}


Object EvaluationContext::finalize_object() {
    auto retval = Object::map(std::move(objects.back()));
    objects.pop_back();
    return retval;
}
