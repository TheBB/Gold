#include <algorithm>
#include <iterator>
#include <iostream>

#include <fmt/core.h>

#include "gold.hpp"

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
        [](Closure) { return "closure"; }
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
        [](Closure) { return Type::closure; }
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


Object Object::operator<(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return Object::boolean(a < b); },
        [](Floating a, Integer b) { return Object::boolean(a < b); },
        [](Integer a, Floating b) { return Object::boolean(a < b); },
        [](Floating a, Floating b) { return Object::boolean(a < b); },
        [](String a, String b) { return Object::boolean(a < b); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `<`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


Object Object::operator<=(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return Object::boolean(a <= b); },
        [](Floating a, Integer b) { return Object::boolean(a <= b); },
        [](Integer a, Floating b) { return Object::boolean(a <= b); },
        [](Floating a, Floating b) { return Object::boolean(a <= b); },
        [](String a, String b) { return Object::boolean(a <= b); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `<=`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


Object Object::operator>(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return Object::boolean(a > b); },
        [](Floating a, Integer b) { return Object::boolean(a > b); },
        [](Integer a, Floating b) { return Object::boolean(a > b); },
        [](Floating a, Floating b) { return Object::boolean(a > b); },
        [](String a, String b) { return Object::boolean(a > b); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `>`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


Object Object::operator>=(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return Object::boolean(a >= b); },
        [](Floating a, Integer b) { return Object::boolean(a >= b); },
        [](Integer a, Floating b) { return Object::boolean(a >= b); },
        [](Floating a, Floating b) { return Object::boolean(a >= b); },
        [](String a, String b) { return Object::boolean(a >= b); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `>=` `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


Object Object::operator==(Object other) const {
    return Object::boolean(std::visit(overloaded {
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
    }, _data, other._data));
}


Object Object::operator!=(Object other) const {
    return Object::boolean(!(bool)(*this == other));
}


Object Object::operator()(EvaluationContext& ctx, const std::vector<Object>& args) const {
    if (type() != Type::closure)
        throw EvalException(fmt::format("attempted to call non-function: `{}`", type_name()));
    auto closure = unsafe_closure();

    if (args.size() != closure->parameters.size())
        throw EvalException(fmt::format(
            "wrong number of parameters: got {} but expected {}",
            args.size(), closure->parameters.size()
        ));

    ctx.push_namespace(closure->nonlocals);
    ctx.push_namespace();

    Object retval;

    try {
        auto id_it = closure->parameters.begin();
        auto arg_it = args.begin();
        while (id_it != closure->parameters.end() && arg_it != args.end())
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


size_t Object::size() const {
    return std::visit(overloaded {
        [](List x) { return x->size(); },
        [](Map x) { return x->size(); },
        [this](auto&&) -> size_t {
            throw EvalException(fmt::format("unsuppurted type for size(): `{}`", type_name()));
        }
    }, _data);
}


std::ostream& operator<<(std::ostream& os, const Object& obj) {
    obj.dump(os);
    return os;
}


void Object::dump(std::ostream& os) const {
    std::visit(overloaded {
        [&os](Integer x) { os << x; },
        [&os](String x) { os << '"' << x << '"'; },
        [&os](Boolean x) { os << (x ? "true" : "false"); },
        [&os](Floating x) { os << fmt::format("{}", x); },
        [&os](Null) { os << "null"; },
        [&os](Closure) { os << "<closure>"; },
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


void EvaluationContext::assign_object(const std::string& key, Object value) {
    objects.back()[key] = value;
}


Object EvaluationContext::finalize_object() {
    auto retval = Object::map(std::move(objects.back()));
    objects.pop_back();
    return retval;
}
