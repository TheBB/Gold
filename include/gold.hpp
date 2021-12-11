#include <functional>
#include <list>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <variant>
#include <vector>

#pragma once


namespace Gold {


class EvaluationContext;
class Object;
class Namespace : public std::map<std::string, Object> {
public:
    Namespace() : std::map<std::string, Object>() {}
    Namespace(std::initializer_list<value_type> list) : std::map<std::string, Object>(list) {}
};


extern Namespace builtins;


struct Source {
    size_t byte;
    size_t line;
    size_t column;

    void serialize(std::ostream&) const;
    static Source deserialize(std::istream&);
};


class AstNode {
private:
    Source src;
public:
    AstNode(Source source) : src(source) {}
    virtual void dump(std::ostream&) const = 0;
    std::string dump() const;
    virtual void free_identifiers(std::set<std::string>&) const = 0;
    std::set<std::string> free_identifiers() const;
    virtual Object evaluate(EvaluationContext&) const = 0;
    Object evaluate() const;

    std::string serialize() const;
    virtual void serialize(std::ostream&) const = 0;
    static std::unique_ptr<AstNode> deserialize(std::string);
    static std::unique_ptr<AstNode> deserialize(std::istream&);

    const Source source() const { return src; }
};


class Object {
public:
    enum class Type { integer, string, null, boolean, floating, map, list, closure, builtin };

    using Null = std::monostate;

    using Integer = intmax_t;
    using String = std::string;
    using Boolean = bool;
    using Floating = double;

    using MapT = std::map<std::string, Object>;
    using Map = std::shared_ptr<MapT>;
    using ListT = std::vector<Object>;
    using List = std::shared_ptr<ListT>;

    using ClosureT = struct {
        Namespace nonlocals;
        std::vector<std::string> parameters;
        std::unique_ptr<AstNode> expression;
    };
    using Closure = std::shared_ptr<ClosureT>;

    using Builtin = struct {
        std::string name;
        std::function<Object(EvaluationContext& ctx, const std::vector<Object>&)> callable;
    };

    using Variant = std::variant<Null, Integer, String, Boolean, Floating, Map, List, Closure, Builtin>;

private:
     Variant _data;

public:
    // Raw constructors
    Object() : _data() {}
    explicit Object(Null value) : _data(value) {}
    explicit Object(Integer value) : _data(value) {}
    explicit Object(const String& value) : _data(value) {}
    explicit Object(Boolean value) : _data(value) {}
    explicit Object(Floating value) : _data(value) {}
    explicit Object(const Map& value) : _data(value) {}
    explicit Object(const List& value) : _data(value) {}
    explicit Object(Closure value) : _data(value) {}
    explicit Object(Builtin value) : _data(value) {}

    // Explicit constructors
    static Object null() { return Object(); }
    static Object integer(Integer value) { return Object(value); }
    static Object string(const String& value) { return Object(value); }
    static Object boolean(Boolean value) { return Object(value ? true : false); }
    static Object floating(Floating value) { return Object(value); }

    static Object map(Map value) { return Object(value); }
    static Object map(MapT value) { return Object(std::make_shared<MapT>(value)); }
    static Object map(MapT& value) { return Object(std::make_shared<MapT>(value)); }

    static Object list(List value) { return Object(value); }
    static Object list(ListT value) { return Object(std::make_shared<ListT>(value)); }
    static Object list(ListT& value) { return Object(std::make_shared<ListT>(value)); }

    static Object closure(Closure value) { return Object(value); }
    static Object builtin(Builtin value) { return Object(value); }

    static Object deserialize(std::string);
    static Object deserialize(std::istream&);

    // Type inspection
    Type type() const;
    std::string type_name() const;
    bool is_null() const { return type() == Type::null; }

    // Unsafe getters
    Integer unsafe_integer() const { return std::get<Integer>(_data); }
    const String& unsafe_string() const { return std::get<String>(_data); }
    Boolean unsafe_boolean() const { return std::get<Boolean>(_data); }
    Floating unsafe_floating() const { return std::get<Floating>(_data); }
    const Map& unsafe_map() const { return std::get<Map>(_data); }
    const List& unsafe_list() const { return std::get<List>(_data); }

    const Variant& data() const { return _data; }

    // Serialization
    std::string serialize() const;
    void serialize(std::ostream&) const;

    // Operators
    Object operator+(Object) const;
    Object operator-(Object) const;
    Object operator*(Object) const;
    Object operator/(Object) const;
    Object operator_idiv(Object) const;
    Object operator<(Object) const;
    Object operator<=(Object) const;
    Object operator>(Object) const;
    Object operator>=(Object) const;
    Object operator==(Object) const;
    Object operator!=(Object) const;

    Object operator()(EvaluationContext&, const std::vector<Object>&) const;

    Object operator[](Object) const;
    Object operator[](intmax_t) const;
    Object operator[](std::string) const;

    explicit operator bool() const;

    // More convenient access
    size_t size() const;

    void dump(std::ostream&) const;
};


struct EvalException: public std::exception {
    bool has_position;
    std::string reason;
    EvalException() : has_position(false), reason("") {}
    EvalException(std::string s) : has_position(false), reason(s) {}
    EvalException(Source src, std::string s) : EvalException(s) { position(src); }
    void position(Source source) noexcept;
    const char* what() const noexcept { return reason.c_str(); }
};


struct InternalException: public std::exception {
    const char* what() const noexcept {
        return "an internal error happened - please report";
    }
};


class EvaluationContext {
private:
    std::list<Namespace> namespaces;
    std::vector<Namespace> objects;
public:
    EvaluationContext() { push_namespace(builtins); }

    Object lookup(const std::string& key);
    Object lookup_object(const std::string& key, int index);
    void assign(const std::string& key, Object value);

    void push_namespace(Namespace ns) { namespaces.push_front(ns); }
    void push_namespace() { namespaces.emplace_front(); }
    void pop_namespace(int num = 1) { for (int i = 0; i < num; i++ ) namespaces.pop_front(); }

    void push_object() { objects.emplace_back(); }
    void assign_object(const std::string& key, Object value);
    Object finalize_object();
};


Object evaluate_string(std::string);


}

std::ostream& operator<<(std::ostream&, const Gold::Object&);
