#include <functional>
#include <list>
#include <map>
#include <memory>
#include <optional>
#include <set>
#include <sstream>
#include <variant>
#include <vector>

#pragma once


namespace Gold {


class EvaluationContext;
class Object;
class Serializer;
class Deserializer;

using Namespace = std::map<std::string, Object>;
extern Namespace builtins;


struct Source {
    size_t byte;
    size_t line;
    size_t column;
};


class AstNode {
private:
    Source src;
public:
    AstNode(Source source) : src(source) {}
    virtual ~AstNode() {};
    virtual void dump(std::ostream&) const = 0;
    std::string dump() const;
    virtual void free_identifiers(std::set<std::string>&) const = 0;
    std::set<std::string> free_identifiers() const;
    virtual Object evaluate(EvaluationContext&) const = 0;

    std::string serialize() const;
    virtual void serialize(std::ostream&) const;
    virtual void serialize(Serializer&) const = 0;
    static std::unique_ptr<AstNode> deserialize(std::string);
    static std::unique_ptr<AstNode> deserialize(std::istream&);
    static std::unique_ptr<AstNode> deserialize(Deserializer&);

    const Source source() const { return src; }
};

using AstPtr = std::unique_ptr<AstNode>;


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
    bool operator<(Object) const;
    bool operator<=(Object) const;
    bool operator>(Object) const;
    bool operator>=(Object) const;
    bool operator==(Object) const;
    bool operator!=(Object) const;

    Object operator()(EvaluationContext&, const std::vector<Object>&) const;

    Object operator[](Object) const;
    Object operator[](intmax_t) const;
    Object operator[](std::string) const;

    explicit operator bool() const;

    // More convenient access
    size_t size() const;

    void dump(std::ostream&) const;
};


class Serializer {
private:
    std::ostream& os;
public:
    Serializer(std::ostream& stream) : os(stream) {}

    template<typename T>
    Serializer& operator<<(T v) { os.write((const char*) &v, sizeof v); return *this; }

    template<typename T>
    Serializer& operator<<(const std::shared_ptr<T>& v) {
        return *this << *v;
    }

    template<typename T>
    Serializer& operator<<(const std::vector<T>& v) {
        *this << v.size();
        for (auto& c : v)
            *this << c;
        return *this;
    }

    template<typename K, typename V>
    Serializer& operator<<(const std::map<K,V>& m) {
        *this << m.size();
        for (auto& [k, v] : m)
            *this << k << v;
        return  *this;
    }

    Serializer& operator<<(const std::string&);
    Serializer& operator<<(const Object&);
    Serializer& operator<<(const AstNode&);
};


class Deserializer {
private:
    std::istream& is;
public:
    Deserializer(std::istream& stream) : is(stream) {}

    template<typename T>
    T read() {
        T val;
        is.read((char *) &val, sizeof val);
        return val;
    }

    template<typename T>
    std::vector<T> read_vec() {
        auto size = read<size_t>();
        std::vector<T> vec;
        for (size_t i = 0; i < size; i++)
            vec.push_back(read<T>());
        return vec;
    }

    template<typename K, typename V>
    std::map<K,V> read_map() {
        auto size = read<size_t>();
        std::map<K,V> map;
        for (size_t i = 0; i < size; i++) {
            auto key = read<K>();
            auto val = read<V>();
            map[key] = val;
        }
        return map;
    }

    template<typename T>
    Deserializer& operator>>(T& v) { v = read<T>(); return *this; }
};

template<> std::string Deserializer::read<std::string>();
template<> Object Deserializer::read<Object>();
template<> std::unique_ptr<AstNode> Deserializer::read<std::unique_ptr<AstNode>>();


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


class LibFinder {
public:
    virtual ~LibFinder() {};
    virtual std::optional<Object> find(const std::string&) const = 0;
};


class EvaluationContext {
private:
    std::list<Namespace> namespaces;
    std::vector<Namespace> objects;
    std::vector<std::shared_ptr<LibFinder>> libfinders;
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

    void append_libfinder(std::shared_ptr<LibFinder> finder) { libfinders.push_back(std::move(finder)); }
    Object import(const std::string& path) const;
};


void register_stdlib(std::unique_ptr<LibFinder>);
Object evaluate_string(std::string);
Object evaluate_string(EvaluationContext&, std::string);
Object evaluate_file(std::string);
Object evaluate_file(EvaluationContext&, std::string);


}

std::ostream& operator<<(std::ostream&, const Gold::Object&);
std::ostream& operator<<(std::ostream&, const Gold::AstNode&);
