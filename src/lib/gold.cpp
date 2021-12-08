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
    case Type::closure: return "closure";
    case Type::undefined: return "undefined";
    }
    return "??";
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
    return std::get<Evaluator>(_data)(ctx, args);
}


Object Object::operator[](Object index) const {
    if (type() == Object::Type::list && index.type() == Object::Type::integer) {
        auto ix = index.unsafe_integer();
        if (ix < 0 || ix >= (typeof(ix))unsafe_list()->size())
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


std::string Object::serialize() const {
    std::ostringstream os;
    serialize(os);
    return os.str();
}


template <typename T>
static void write(std::ostream& os, const T val) {
    os.write((const char*) &val, sizeof val);
}


template <typename T>
static T read(std::istream& is) {
    T val;
    is.read((char *) &val, sizeof val);
    return val;
}


static void write_str(std::ostream& os, const std::string& val) {
    auto size = val.size();
    write(os, size);
    os.write(val.c_str(), size);
}


static std::string read_str(std::istream& is) {
    size_t size = read<size_t>(is);
    char* data = new char[size];
    is.read(data, size);
    std::string retval(data, size);
    delete[] data;
    return retval;
}


void Object::serialize(std::ostream& os) const {
    switch (type()) {
    case Type::integer:
        os << 'I';
        write(os, unsafe_integer());
        break;
    case Type::string:
        os << 'S';
        write_str(os, unsafe_string());
        break;
    case Type::boolean:
        os << 'B' << (unsafe_boolean() ? '1' : '0');
        break;
    case Type::floating:
        os << 'F';
        write(os, unsafe_floating());
        break;
    case Type::map:
        os << 'M';
        write(os, unsafe_map()->size());
        for (auto& [key, value] : *unsafe_map()) {
            write_str(os, key);
            value.serialize(os);
        }
        break;
    case Type::list:
        os << 'L';
        write(os, unsafe_list()->size());
        for (auto& value : *unsafe_list())
            value.serialize(os);
        break;
    case Type::undefined:
        os << 'U';
        break;
    }
}


Object Object::deserialize(std::string val) {
    std::istringstream is(val);
    return deserialize(is);
}


Object Object::deserialize(std::istream& is) {
    char indicator;
    is >> indicator;
    switch (indicator) {
    case 'I':
        return Object::integer(read<Integer>(is));
    case 'S':
        return Object::string(read_str(is));
    case 'B': {
        char val;
        is >> val;
        return Object::boolean(val == '1' ? true : false);
    }
    case 'F':
        return Object::floating(read<double>(is));
    case 'M': {
        auto size = read<size_t>(is);
        Object::MapT map;
        for (size_t i = 0; i < size; i++) {
            auto key = read_str(is);
            auto val = Object::deserialize(is);
            map[key] = val;
        }
        return Object::map(std::move(map));
    }
    case 'L': {
        auto size = read<size_t>(is);
        Object::ListT list;
        for (size_t i = 0; i < size; i++)
            list.push_back(Object::deserialize(is));
        return Object::list(std::move(list));
    }
    case 'U':
        return Object::undefined();
    }
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
    case Object::Type::closure:
        os << "<closure>";
        break;
    case Object::Type::undefined:
        os << "<undefined>";
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
