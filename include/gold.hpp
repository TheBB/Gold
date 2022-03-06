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


template<typename T>
using sptr = std::shared_ptr<T>;

template<typename T>
using uptr = std::unique_ptr<T>;

template<typename T>
using opt = std::optional<T>;


class EvaluationContext;
class Object;
class Serializer;
class Deserializer;
struct AstNode;
struct Binding;


using AstPtr = uptr<AstNode>;
using BindingPtr = uptr<Binding>;
using Namespace = std::map<std::string, Object>;
extern Namespace builtins;


class Serializable {
public:
    std::string serialize() const;
    void serialize(std::ostream& os) const;
    void serialize(Serializer& os) const;
private:
    virtual void do_serialize(Serializer&) const = 0;
};


struct Source {
    size_t byte;
    size_t line;
    size_t column;
};


struct InternalException: public std::exception {
    std::string msg;
    InternalException() : msg("an internal error happend - please report") {}
    InternalException(std::string s) : msg(s) {}

    const char* what() const noexcept {
        return msg.c_str();
    }
};


struct EvalException: public std::exception {
    std::vector<Source> positions;
    std::vector<std::string> lines;
    std::string reason;
    opt<std::string> message;

    EvalException() : reason("") {}
    EvalException(std::string_view reason) : reason(reason) {}
    EvalException(Source src, std::string reason) : positions({src}), reason(reason) {}

    void tag_position(Source, bool = false) noexcept;
    void tag_lines(std::function<std::string_view(Source&)>) noexcept;

    const char* what() const noexcept;
};


struct Binding : public Serializable {
    Source src;

    Binding(Source src) : src(src) {}
    virtual ~Binding() {}

    bool bind(EvaluationContext&, Object, bool = true) const;
    virtual bool do_bind(EvaluationContext&, Object) const = 0;

    virtual BindingPtr freeze(EvaluationContext& ctx) const = 0;

    std::pair<std::set<std::string>, std::set<std::string>> free_and_bound() const;
    virtual void free_and_bound(std::set<std::string>&, std::set<std::string>&) const = 0;

    static BindingPtr deserialize(Deserializer&);

    virtual void dump(std::ostream&) const = 0;
    friend std::ostream& operator<<(std::ostream& os, const Binding& binding) { binding.dump(os); return os; }
};


class Object : public Serializable {
public:
    enum class Type { integer, string, null, boolean, floating, map, list, closure, builtin };

    using Null = std::monostate;

    using Integer = intmax_t;
    using String = std::string;
    using Boolean = bool;
    using Floating = double;

    using MapT = std::map<std::string, Object>;
    using Map = sptr<MapT>;
    using ListT = std::vector<Object>;
    using List = sptr<ListT>;

    using ClosureT = struct {
        Namespace nonlocals;
        sptr<Binding> parameters;
        sptr<AstNode> expression;
    };
    using Closure = sptr<ClosureT>;

    using Builtin = struct {
        std::string name;
        std::function<Object(EvaluationContext&, const std::vector<Object>&)> callable;
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

    static Object list(List value) { return Object(value); }
    static Object list(ListT value) { return Object(std::make_shared<ListT>(value)); }

    static Object closure(Closure value) { return Object(value); }
    static Object builtin(Builtin value) { return Object(value); }

    static Object deserialize(std::string);
    static Object deserialize(std::istream&);
    static Object deserialize(Deserializer&);

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
    virtual void do_serialize(Serializer&) const;

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

    Object operator()(const std::vector<Object>&) const;
    Object operator()(EvaluationContext&, const std::vector<Object>&) const;

    Object operator[](Object) const;
    Object operator[](intmax_t) const;
    Object operator[](std::string) const;

    explicit operator bool() const;

    // More convenient access
    size_t size() const;

    friend std::ostream& operator<<(std::ostream& os, const Object& obj) { obj.dump(os); return os; }
    void dump(std::ostream&) const;
    std::string dump() const;
};


class Serializer {
private:
    std::ostream& os;
    std::map<void*, intmax_t> pointers;

public:
    explicit Serializer(std::ostream& stream) : os(stream) {}

    template<
        typename T,
        std::enable_if_t<!std::is_base_of<Serializable, T>::value, bool> = true
    >
    Serializer& operator<<(T v) {
        os.write((const char*) &v, sizeof v); return *this;
    }

    template<typename T>
    Serializer& operator<<(const sptr<T>& v) {
        write(v, [this](const T& v) { *this << v; });
        return *this;
    }

    template<typename T>
    Serializer& operator<<(const uptr<T>& v) {
        return *this << *v;
    }

    template<typename T>
    Serializer& operator<<(const std::vector<T>& v) {
        write(v, [this](const T& c) { *this << c; });
        return *this;
    }

    template<typename K, typename V>
    Serializer& operator<<(const std::map<K,V>& m) {
        write(m, [this](const K& k, const V& v) { *this << k << v; });
        return *this;
    }

    template<typename T>
    Serializer& operator<<(const opt<T>& v) {
        if (!v.has_value())
            return *this << 'N';
        return *this << 'Y' << v.value();
    }

    Serializer& operator<<(const std::string&);

    Serializer& operator<<(const Serializable& obj) {
        obj.serialize(*this);
        return *this;
    }

    template<typename T, typename F>
    void write(const sptr<T>& v, F writer) {
        void* ptr = v.get();
        auto entry = pointers.find(ptr);
        if (entry == pointers.end()) {
            intmax_t id = pointers.size();
            pointers[ptr] = id;
            *this << 'D' << id;
            writer(*v);
        }
        else
            *this << 'R' << entry->second;
    }

    template<typename T, typename F>
    void write(const std::vector<T>& v, F writer) {
        *this << v.size();
        for (auto& c : v)
            writer(c);
    }

    template<typename K, typename V, typename F>
    void write(const std::map<K,V>& m, F writer) {
        *this << m.size();
        for (auto& [k, v] : m)
            writer(k, v);
    }
};


class Deserializer {
private:
    std::istream& is;
    std::map<intmax_t, sptr<void>> pointers;

    template<typename T>
    void readref(T& val) { is.read((char *) &val, sizeof val); }

    template<typename T>
    void readref(T*& val) { val = new T; readref(*val); }

    template<typename T, typename F>
    void readref(T*& val, F f) { val = new T; readref(*val, f); }

    template<typename T>
    void readref(opt<T>& val) {
        if (read<char>() == 'Y')
            val = read<T>();
    }

    template<typename T, typename F>
    void readref(opt<T>& val, F f) {
        if (read<char>() == 'Y')
            val = f();
    }

    void readref(std::string&);

    template<typename V, typename F>
    void readref(std::vector<V>& v, F f) {
        auto size = read<size_t>();
        v.resize(size);
        for (size_t i = 0; i < size; i++)
            v[i] = f();
    }

    template<typename V>
    void readref(std::vector<V>& v) {
        readref(v, [this](){ return read<V>(); });
    }

    template<typename K, typename V, typename F>
    void readref(std::map<K,V>& m, F f) {
        auto size = read<size_t>();
        m.clear();
        for (size_t i = 0; i < size; i++) {
            K key; V val;
            std::tie(key, val) = f();
            m[key] = val;
        }
    }

    template<typename K, typename V>
    void readref(std::map<K,V>& m) {
        readref(m, [this]() {
            auto key = read<K>();
            auto value = read<V>();
            return std::pair<K,V> { key, value };
        });
    }

    template<typename T>
    void readref(sptr<T>& p) {
        auto k = read<char>();
        auto id = read<intmax_t>();
        if (k == 'R')
            p = std::static_pointer_cast<T>(pointers[id]);
        else {
            p = sptr<T>(read<T*>());
            pointers[id] = p;
        }
    }

    template<typename T, typename F>
    void readref(sptr<T>& p, F f) {
        auto k = read<char>();
        auto id = read<intmax_t>();
        if (k == 'R')
            p = std::static_pointer_cast<T>(pointers[id]);
        else {
            // p = sptr<T>(read<T*>(f));
            p = sptr<T>(f());
            pointers[id] = p;
        }
    }

    template<typename T>
    void readref(uptr<T>& p) {
        p = uptr<T>(read<T*>());
    }

    template<typename T, typename F>
    void readref(uptr<T>& p, F f) {
        p = uptr<T>(read<T*>(f));
    }

public:
    Deserializer(std::istream& stream) : is(stream) {}

    template<typename T>
    T read() { T val; readref(val); return val; }

    template<typename T, typename F>
    T read(F f) { T val; readref(val, f); return val; }

    template<typename T>
    Deserializer& operator>>(T& v) { readref(v); return *this; }
};


class LibFinder {
public:
    virtual ~LibFinder() {};
    virtual opt<Object> find(const std::string&) const = 0;
};


class EvaluationContext {
private:
    std::list<Namespace> namespaces;
    std::vector<Namespace> objects;
    std::vector<sptr<LibFinder>> libfinders;

public:
    EvaluationContext() { push_namespace(builtins); }

    Object lookup(const std::string& key);
    opt<Object> weak_lookup(const std::string& key);
    Object lookup_object(const std::string& key, int index);
    void assign(const std::string& key, Object value);

    void push_namespace(Namespace ns) { namespaces.push_front(ns); }
    void push_namespace() { namespaces.emplace_front(); }
    void pop_namespace(int num = 1) { for (int i = 0; i < num; i++ ) namespaces.pop_front(); }
    void collapse_namespace();

    void push_object() { objects.emplace_back(); }
    void assign_object(const std::string& key, Object value);
    Object finalize_object();

    void append_libfinder(sptr<LibFinder> finder) { libfinders.push_back(std::move(finder)); }
    virtual Object import(const std::string& path) const;
};


class ForwardContext : public EvaluationContext {
private:
    EvaluationContext& ctx;
public:
    ForwardContext(EvaluationContext& ctx) : EvaluationContext(), ctx(ctx) {}
    virtual Object import(const std::string& path) const { return ctx.import(path); }
};


void register_stdlib(uptr<LibFinder>);
Object evaluate_string(std::string);
Object evaluate_string(EvaluationContext&, std::string);
Object evaluate_file(std::string);
Object evaluate_file(EvaluationContext&, std::string);


} // Namespace Gold
