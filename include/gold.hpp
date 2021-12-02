#include <map>
#include <memory>
#include <variant>
#include <vector>

#pragma once


namespace Gold {


enum Type { integer, string, boolean, floating, map, list, function, error };

class Object {
public:
    using Integer = intmax_t;
    using String = std::string;
    using Boolean = bool;
    using Floating = double;
    using Error = std::pair<std::string, std::string>;

    using MapT = std::map<std::string, Object>;
    using Map = std::shared_ptr<MapT>;
    using ListT = std::vector<Object>;
    using List = std::shared_ptr<ListT>;

private:
    std::variant<Integer, String, Boolean, Floating, Map, List, Error> _data;

public:
    // Raw constructors
    Object(Integer value) : _data(value) {}
    Object(const String& value) : _data(value) {}
    Object(Boolean value) : _data(value) {}
    Object(Floating value) : _data(value) {}
    Object(const Map& value) : _data(value) {}
    Object(const List& value) : _data(value) {}
    Object(const String& type, const String& message) : _data(Error(type, message)) {}

    // Explicit constructors
    static Object integer(Integer value) { return Object(value); }
    static Object string(const String& value) { return Object(value); }
    static Object boolean(Boolean value) { return Object(value); }
    static Object floating(Floating value) { return Object(value); }
    static Object error(const String& type, const String& message) { return Object(type, message); }

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
        return Type::error;
    }

    std::string type_name() const;
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
};

}

std::ostream& operator<<(std::ostream&, const Gold::Object&);
