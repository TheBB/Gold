#include <list>
#include <map>
#include <memory>
#include <variant>
#include <vector>

#pragma once


namespace Gold {


class EvaluationContext;


class Object {
public:
    enum class Type { undefined, integer, string, boolean, floating, map, list, closure, error };

    using Undefined = std::monostate;

    using Integer = intmax_t;
    using String = std::string;
    using Boolean = bool;
    using Floating = double;
    using Error = std::pair<std::string, std::string>;

    using MapT = std::map<std::string, Object>;
    using Map = std::shared_ptr<MapT>;
    using ListT = std::vector<Object>;
    using List = std::shared_ptr<ListT>;

    using Evaluator = Object (*)(EvaluationContext&, const std::vector<Object>&);

private:
    std::variant<Undefined, Integer, String, Boolean, Floating, Map, List, Evaluator, Error> _data;

public:
    // Raw constructors
    Object() : _data() {}
    Object(Integer value) : _data(value) {}
    Object(const String& value) : _data(value) {}
    Object(Boolean value) : _data(value) {}
    Object(Floating value) : _data(value) {}
    Object(const Map& value) : _data(value) {}
    Object(const List& value) : _data(value) {}
    Object(const String& type, const String& message) : _data(Error(type, message)) {}
    Object(Evaluator eval) : _data(eval) {}

    // Explicit constructors
    static Object undefined() { return Object(); }
    static Object integer(Integer value) { return Object(value); }
    static Object string(const String& value) { return Object(value); }
    static Object boolean(Boolean value) { return Object(value); }
    static Object floating(Floating value) { return Object(value); }
    static Object error(const String& type, const String& message) { return Object(type, message); }
    static Object closure(Evaluator eval) { return Object(eval); }

    static Object map(Map value) { return Object(value); }
    static Object map(MapT value) { return Object(std::make_shared<MapT>(value)); }
    static Object map(MapT& value) { return Object(std::make_shared<MapT>(value)); }

    static Object list(List value) { return Object(value); }
    static Object list(ListT value) { return Object(std::make_shared<ListT>(value)); }
    static Object list(ListT& value) { return Object(std::make_shared<ListT>(value)); }

    // Type inspection
    Type type() const {
        if (std::holds_alternative<Integer>(_data)) return Type::integer;
        if (std::holds_alternative<String>(_data)) return Type::string;
        if (std::holds_alternative<Boolean>(_data)) return Type::boolean;
        if (std::holds_alternative<Floating>(_data)) return Type::floating;
        if (std::holds_alternative<Map>(_data)) return Type::map;
        if (std::holds_alternative<List>(_data)) return Type::list;
        if (std::holds_alternative<Evaluator>(_data)) return Type::closure;
        if (std::holds_alternative<Undefined>(_data)) return Type::undefined;
        return Type::error;
    }

    std::string type_name() const;
    bool is_undefined() const { return type() == Type::undefined; }
    bool is_error() const { return type() == Type::error; }

    // Unsafe getters
    Integer unsafe_integer() const { return std::get<Integer>(_data); }
    const String& unsafe_string() const { return std::get<String>(_data); }
    Boolean unsafe_boolean() const { return std::get<Boolean>(_data); }
    Floating unsafe_floating() const { return std::get<Floating>(_data); }
    const Map& unsafe_map() const { return std::get<Map>(_data); }
    const List& unsafe_list() const { return std::get<List>(_data); }
    const Error& unsafe_error() const { return std::get<Error>(_data); }

    // Operators
    Object operator+(Object other);
    Object operator-(Object other);
    Object operator()(EvaluationContext&, const std::vector<Object>&);
};


struct EvalException: public std::exception {};


class Namespace : public std::map<std::string, Object> {};


class EvaluationContext {
private:
    std::list<Namespace> namespaces;
    std::vector<Namespace> objects;
public:
    Object lookup(std::string& key);
    Object lookup_object(std::string& key, int index);
};



}

std::ostream& operator<<(std::ostream&, const Gold::Object&);
