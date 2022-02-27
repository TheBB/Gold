#include <algorithm>
#include <cinttypes>
#include <filesystem>
#include <iterator>
#include <iostream>

#include <fmt/core.h>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


std::string Object::type_name() const {
    return std::visit(overloaded {
        [](Null) { return "null"; },
        [](Integer) { return "integer"; },
        [](String) { return "string"; },
        [](Boolean) { return "boolean"; },
        [](Floating) { return "floating"; },
        [](Map) { return "map"; },
        [](List) { return "list"; },
        [](Closure) { return "function"; },
        [](Builtin) { return "function"; }
    }, _data);
}


Object::Type Object::type() const {
    return std::visit(overloaded {
        [](Null) { return Type::null; },
        [](Integer) { return Type::integer; },
        [](String) { return Type::string; },
        [](Boolean) { return Type::boolean; },
        [](Floating) { return Type::floating; },
        [](Map) { return Type::map; },
        [](List) { return Type::list; },
        [](Closure) { return Type::closure; },
        [](Builtin) { return Type::builtin; }
    }, _data);
}


Object Object::operator+(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return Object::integer(a + b); },
        [](Integer a, Floating b) { return Object::floating(a + b); },
        [](Floating a, Integer b) { return Object::floating(a + b); },
        [](Floating a, Floating b) { return Object::floating(a + b); },
        [](String a, String b) { return Object::string(a + b); },
        [](List a, List b) {
            List elements = std::make_shared<std::vector<Object>>();
            std::copy(a->begin(), a->end(), std::back_inserter(*elements));
            std::copy(b->begin(), b->end(), std::back_inserter(*elements));
            return Object::list(elements);
        },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `+`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


Object Object::operator-(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return Object::integer(a - b); },
        [](Floating a, Integer b) { return Object::floating(a - b); },
        [](Integer a, Floating b) { return Object::floating(a - b); },
        [](Floating a, Floating b) { return Object::floating(a - b); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `-`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


Object Object::operator*(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return Object::integer(a * b); },
        [](Floating a, Integer b) { return Object::floating(a * b); },
        [](Integer a, Floating b) { return Object::floating(a * b); },
        [](Floating a, Floating b) { return Object::floating(a * b); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `*`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


Object Object::operator/(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return Object::floating((double)a / b); },
        [](Floating a, Integer b) { return Object::floating(a / b); },
        [](Integer a, Floating b) { return Object::floating(a / b); },
        [](Floating a, Floating b) { return Object::floating(a / b); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `/`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


Object Object::operator_idiv(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return Object::integer(a / b); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `//`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


bool Object::operator<(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return a < b; },
        [](Floating a, Integer b) { return a < b; },
        [](Integer a, Floating b) { return a < b; },
        [](Floating a, Floating b) { return a < b; },
        [](String a, String b) { return a < b; },
        [this, other](auto&&, auto&&) -> bool {
            throw EvalException(fmt::format(
                "unsupported types for operator `<`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


bool Object::operator<=(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return a <= b; },
        [](Floating a, Integer b) { return a <= b; },
        [](Integer a, Floating b) { return a <= b; },
        [](Floating a, Floating b) { return a <= b; },
        [](String a, String b) { return a <= b; },
        [this, other](auto&&, auto&&) -> bool {
            throw EvalException(fmt::format(
                "unsupported types for operator `<=`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


bool Object::operator>(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return a > b; },
        [](Floating a, Integer b) { return a > b; },
        [](Integer a, Floating b) { return a > b; },
        [](Floating a, Floating b) { return a > b; },
        [](String a, String b) { return a > b; },
        [this, other](auto&&, auto&&) -> bool {
            throw EvalException(fmt::format(
                "unsupported types for operator `>`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


bool Object::operator>=(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return a >= b; },
        [](Floating a, Integer b) { return a >= b; },
        [](Integer a, Floating b) { return a >= b; },
        [](Floating a, Floating b) { return a >= b; },
        [](String a, String b) { return a >= b; },
        [this, other](auto&&, auto&&) -> bool {
            throw EvalException(fmt::format(
                "unsupported types for operator `>=` `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


bool Object::operator==(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return a == b; },
        [](Floating a, Integer b) { return a == b; },
        [](Integer a, Floating b) { return a == b; },
        [](Floating a, Floating b) { return a == b; },
        [](String a, String b) { return a == b; },
        [](Boolean a, Boolean b) { return a == b; },
        [](Null, Null) { return true; },
        [](Map a, Map b) { return *a == *b; },
        [](List a, List b) { return *a == *b; },
        [](auto&&, auto&&) { return false; }
    }, _data, other._data);
}


bool Object::operator!=(Object other) const {
    return !(*this == other);
}


Object Object::operator()(EvaluationContext& ctx, const std::vector<Object>& args) const {
    if (type() == Type::builtin)
        return std::get<Builtin>(_data).callable(ctx, args);
    if (type() != Type::closure)
        throw EvalException(fmt::format("attempted to call non-function: `{}`", type_name()));
    auto closure = std::get<Closure>(_data);

    if (args.size() != closure->parameters->size())
        throw EvalException(fmt::format(
            "wrong number of parameters: got {} but expected {}",
            args.size(), closure->parameters->size()
        ));

    ctx.push_namespace(closure->nonlocals);
    ctx.push_namespace();

    Object retval;

    try {
        auto id_it = closure->parameters->begin();
        auto arg_it = args.begin();
        while (id_it != closure->parameters->end() && arg_it != args.end())
            ctx.assign(*id_it++, *arg_it++);
        retval = closure->expression->evaluate(ctx);
    }
    catch (const std::exception&) {
        ctx.pop_namespace();
        throw;
    }

    ctx.pop_namespace(2);
    return retval;
}


Object Object::operator[](Object index) const {
    return std::visit(overloaded {
        [this](Integer x) { return (*this)[x]; },
        [this](String x) { return (*this)[x]; },
        [&index](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported subscript type: `{}`", index.type_name()));
        }
    }, index._data);
}


Object Object::operator[](intmax_t index) const {
    if (type() != Object::Type::list)
        throw EvalException(fmt::format("unsupported type for integer subscripting: `{}`", type_name()));
    if (index < 0)
        throw EvalException(fmt::format("list index out of range: {}", index));
    auto& list = unsafe_list();
    if ((size_t)index >= unsafe_list()->size())
        throw EvalException(fmt::format("list index out of range: {} > {}", index, unsafe_list()->size()));
    return (*list)[index];
}


Object Object::operator[](std::string index) const {
    if (type() != Object::Type::map)
        throw EvalException(fmt::format("unsupported type for string subscripting: `{}`", type_name()));
    auto& map = unsafe_map();
    if (map->find(index) == unsafe_map()->end())
        throw EvalException(fmt::format("key not found: {}", index));
    return (*map)[index];
}


Object::operator bool() const {
    return std::visit(overloaded {
        [](Null x) { return false; },
        [](Boolean x) { return x; },
        [](auto&&) { return true; }
    }, _data);
}


size_t Object::size() const {
    return std::visit(overloaded {
        [](List x) { return x->size(); },
        [](Map x) { return x->size(); },
        [this](auto&&) -> size_t {
            throw EvalException(fmt::format("unsuppurted type for size(): `{}`", type_name()));
        }
    }, _data);
}


void Object::dump(std::ostream& os) const {
    std::visit(overloaded {
        [&os](Integer x) { os << x; },
        [&os](String x) {
            os << '"';
            for (char c : x) {
                switch (c) {
                case '\b': os << "\\b"; break;
                case '\f': os << "\\f"; break;
                case '\n': os << "\\n"; break;
                case '\r': os << "\\r"; break;
                case '\t': os << "\\t"; break;
                case '"': os << "\\\""; break;
                case '\\': os << "\\\\"; break;
                default: os << c;
                }
            }
            os << '"';
        },
        [&os](Boolean x) { os << (x ? "true" : "false"); },
        [&os](Floating x) { os << fmt::format("{:#}", x); },
        [&os](Null) { os << "null"; },
        [&os](Closure) { os << "<closure>"; },
        [&os](Builtin) { os << "<builtin>"; },
        [&os](List x) {
            os << "[";
            bool first = true;
            for (auto obj : *x) {
                if (!first)
                    os << ", ";
                os << obj;
                first = false;
            }
            os << "]";
        },
        [&os](Map x) {
            os << "{";
            bool first = true;
            for (auto const& [key, val] : *x) {
                if (!first)
                    os << ", ";
                os << key << ": " << val;
                first = false;
            }
            os << "}";
        }
    }, _data);
}


void EvalException::position(Source source) noexcept {
    if (!has_position)
        reason = fmt::format("at {}:{}: {}", source.line, source.column, reason);
    has_position = true;
}


static std::unique_ptr<std::vector<std::unique_ptr<LibFinder>>> _stdlibs = nullptr;

std::vector<std::unique_ptr<LibFinder>>& stdlibs() {
    if (!_stdlibs)
        _stdlibs = std::make_unique<std::vector<std::unique_ptr<LibFinder>>>();
    return *_stdlibs;
}

void Gold::register_stdlib(std::unique_ptr<LibFinder> finder) {
    stdlibs().push_back(std::move(finder));
}


Object EvaluationContext::import(const std::string& path) const {
    for (auto& finder : stdlibs()) {
        auto result = finder->find(path);
        if (result.has_value())
            return result.value();
    }
    for (auto& finder : libfinders) {
        auto result = finder->find(path);
        if (result.has_value())
            return result.value();
    }
    throw EvalException(fmt::format("cannot locate file: {}", path));
}


Object EvaluationContext::lookup(const std::string& key) {
    for (auto& ns : namespaces) {
        if (ns.find(key) == ns.end())
            continue;
        return ns[key];
    }
    throw EvalException(fmt::format("unbound name: `{}`", key));
}


Object EvaluationContext::lookup_object(const std::string& key, int index) {
    auto& ns = objects[objects.size() - index];
    if (ns.find(key) == ns.end()) {
        std::ostringstream os;
        for (int i = 0; i < index; i++)
            os << '.';
        throw EvalException(fmt::format("unbound key: `{}{}`", os.str(), key));
    }
    return ns[key];
}


void EvaluationContext::assign(const std::string& key, Object value) {
    namespaces.front()[key] = value;
}


void EvaluationContext::collapse_namespace() {
    auto& next_ns = *std::next(namespaces.begin());
    for (auto const& [key, val] : namespaces.front())
        next_ns[key] = val;
    namespaces.pop_front();
}


void EvaluationContext::assign_object(const std::string& key, Object value) {
    objects.back()[key] = value;
}


Object EvaluationContext::finalize_object() {
    auto retval = Object::map(std::move(objects.back()));
    objects.pop_back();
    return retval;
}


static Object builtin_int(EvaluationContext&, const std::vector<Object>& args) {
    Object arg = args[0];
    return std::visit(overloaded {
        [&arg](Object::Integer x) { return arg; },
        [](Object::Floating x) { return Object::integer((intmax_t)x); },
        [](Object::Boolean x) { return Object::integer(x ? 1 : 0); },
        [](Object::String x) {
            return Object::integer(std::strtoimax(x.c_str(), nullptr, 10));
        },
        [&arg](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `int()`: `{}`", arg.type_name()));
        }
    }, arg.data());
}


static Object builtin_bool(EvaluationContext&, const std::vector<Object>& args) {
    Object arg = args[0];
    return std::visit(overloaded {
        [](Object::Integer x) { return Object::boolean(x != 0 ? true : false); },
        [](Object::Floating x) { return Object::boolean(x != 0 ? true : false); },
        [&arg](Object::Boolean x) { return arg; },
        [](Object::Null) { return Object::boolean(false); },
        [](auto&&) { return Object::boolean(true); }
    }, arg.data());
}


static Object builtin_str(EvaluationContext&, const std::vector<Object>& args) {
    Object arg = args[0];
    return std::visit(overloaded {
        [](Object::Integer x) { return Object::string(fmt::format("{}", x)); },
        [](Object::Floating x) { return Object::string(fmt::format("{}", x)); },
        [](Object::Boolean x) { return Object::string(x ? "true" : "false"); },
        [](Object::Null) { return Object::string("null"); },
        [&arg](Object::String) { return arg; },
        [&arg](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `str()`: `{}`", arg.type_name()));
        }
    }, arg.data());
}


static Object builtin_float(EvaluationContext&, const std::vector<Object>& args) {
    Object arg = args[0];
    return std::visit(overloaded {
        [](Object::Integer x) { return Object::floating((double)x); },
        [&arg](Object::Floating x) { return arg; },
        [](Object::Boolean x) { return Object::floating(x ? 1.0 : 0.0); },
        [](Object::String x) { return Object::floating(std::stod(x)); },
        [&arg](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `float()`: `{}`", arg.type_name()));
        }
    }, arg.data());
}


static Object builtin_len(EvaluationContext&, const std::vector<Object>& args) {
    Object arg = args[0];
    return std::visit(overloaded {
        [](Object::List x) { return Object::integer(x->size()); },
        [](Object::Map x) { return Object::integer(x->size()); },
        [&arg](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `len()`: `{}`", arg.type_name()));
        }
    }, arg.data());
}


static Object builtin_range(EvaluationContext&, const std::vector<Object>& args) {
    std::for_each(args.begin(), args.end(), [](auto x) {
        if (x.type() != Object::Type::integer)
            throw EvalException(fmt::format("unsupported type for `range()`: `{}`", x.type_name()));
    });

    intmax_t start, stop;
    if (args.size() == 1) {
        start = 0;
        stop = args[0].unsafe_integer();
    }
    else {
        start = args[0].unsafe_integer();
        stop = args[1].unsafe_integer();
    }

    std::vector<Object> range;
    for (intmax_t i = start; i < stop; i++)
        range.push_back(Object::integer(i));
    return Object::list(std::move(range));
}


static Object builtin_map(EvaluationContext& ctx, const std::vector<Object>& args) {
    Object func = args[0];
    Object sequence = args[1];
    return std::visit(overloaded {
        [&func, &ctx](Object::List x) {
            auto result = std::make_shared<Object::ListT>();
            result->resize(x->size());
            std::transform(
                x->begin(), x->end(), result->begin(),
                [&func, &ctx](Object x) { return func(ctx, {x}); }
            );
            return Object::list(result);
        },
        [&sequence](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `map()`: `{}`", sequence.type_name()));
        }
    }, sequence.data());
}


static Object builtin_filter(EvaluationContext& ctx, const std::vector<Object>& args) {
    Object func = args[0];
    Object sequence = args[1];
    return std::visit(overloaded {
        [&func, &ctx](Object::List x) {
            auto result = std::make_shared<Object::ListT>();
            std::copy_if(
                x->begin(), x->end(), std::back_inserter(*result),
                [&func, &ctx](auto x) { return (bool)func(ctx, {x}); }
            );
            return Object::list(result);
        },
        [&sequence](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `filter()`: `{}`", sequence.type_name()));
        }
    }, sequence.data());
}


static Object builtin_items(EvaluationContext& ctx, const std::vector<Object>& args) {
    Object map = args[0];
    return std::visit(overloaded {
        [](Object::Map x) {
            auto result = std::make_shared<Object::ListT>();
            for (auto& [key, value] : *x) {
                auto pair = std::make_shared<Object::ListT>();
                pair->push_back(Object::string(key));
                pair->push_back(value);
                result->push_back(Object::list(pair));
            }
            return Object::list(result);
        },
        [&map](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `keys()`: `{}`", map.type_name()));
        }
    }, map.data());
}


static Object builtin_import(EvaluationContext& ctx, const std::vector<Object>& args) {
    Object arg = args[0];
    if (arg.type() != Object::Type::string)
        throw EvalException(fmt::format("unsupported type for `import()`: `{}`", arg.type_name()));
    return ctx.import(arg.unsafe_string());
}


#define BUILTIN(x,y) { x, Object(Object::Builtin { x, y })}


Namespace Gold::builtins = {
    BUILTIN("int", builtin_int),
    BUILTIN("bool", builtin_bool),
    BUILTIN("str", builtin_str),
    BUILTIN("float", builtin_float),
    BUILTIN("len", builtin_len),
    BUILTIN("range", builtin_range),
    BUILTIN("map", builtin_map),
    BUILTIN("filter", builtin_filter),
    BUILTIN("items", builtin_items),
    BUILTIN("import", builtin_import),
};
