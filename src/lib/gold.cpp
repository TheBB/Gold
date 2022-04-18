#include <algorithm>
#include <cinttypes>
#include <cmath>
#include <fstream>
#include <iterator>
#include <iostream>
#include <limits>

#include <fmt/core.h>

#include <tao/pegtl.hpp>

#include "gold.hpp"
#include "parsing.hpp"


using namespace Gold;
namespace p = tao::pegtl;

template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;

namespace Gold {
Expr* parse(p::string_input<>& input);
}


mpz_ext mpz_ext::_min = mpz_ext(std::numeric_limits<std::intmax_t>::min());
mpz_ext mpz_ext::_max = mpz_ext(std::numeric_limits<std::intmax_t>::max());


mpz_ext::mpz_ext(std::intmax_t value) : mpz_class() {
    bool add_one, flip;
    if ((add_one = value == std::numeric_limits<std::intmax_t>::min()))
        value++;
    if ((flip = value < 0))
        value = -value;
    mpz_import(get_mpz_t(), 1, -1, sizeof value, 0, 1, &value);
    if (add_one)
        mpz_add_ui(get_mpz_t(), get_mpz_t(), 1);
    if (flip)
        mpz_neg(get_mpz_t(), get_mpz_t());
}


bool mpz_ext::fits_intmax_t() const {
    if (mpz_cmp(get_mpz_t(), _max.get_mpz_t()) > 0)
        return false;
    if (mpz_cmp(get_mpz_t(), _min.get_mpz_t()) < 0)
        return false;
    return true;
}


std::intmax_t mpz_ext::get_intmax_t() const {
    if (mpz_cmp(get_mpz_t(), _min.get_mpz_t()) == 0)
        return std::numeric_limits<std::intmax_t>::min();
    std::intmax_t rval;
    mpz_export(&rval, nullptr, -1, sizeof rval, 0, 0, get_mpz_t());
    if (mpz_sgn(get_mpz_t()) < 0)
        rval = -rval;
    return rval;
}


ExprPtr Gold::parse_string(std::string code) {
    p::string_input input(code, "code");
    return ExprPtr(parse(input));
}


Object Gold::evaluate_string(std::string code) {
    EvaluationContext ctx;
    return evaluate_string(ctx, code);
}


Object Gold::evaluate_string(EvaluationContext& ctx, std::string code) {
    p::string_input input(code, "code");
    auto ast = parse(input);
    try {
        return ast->evaluate(ctx);
    }
    catch (EvalException& e) {
        e.tag_lines([&input](Source& src) {
            return input.line_at(p::position(src.byte, src.line, src.column, ""));
        });
        throw;
    }
}


Object Gold::evaluate_file(std::string path) {
    EvaluationContext ctx;
    return evaluate_file(ctx, path);
}


Object Gold::evaluate_file(EvaluationContext& ctx, std::string path) {
    auto fpath = ctx.path_to(filesystem::path(path));
    if (!filesystem::exists(fpath))
        throw EvalException(fmt::format("unable to find file '{}'", path));
    ctx.push_path(fpath);
    std::ifstream file(fpath.string());
    if (!file.is_open()) {
        ctx.pop_path();
        throw EvalException(fmt::format("unable to open file '{}'", path));
    }
    std::stringstream buffer;
    buffer << file.rdbuf();
    if (file.fail()) {
        ctx.pop_path();
        throw EvalException(fmt::format("error occured while reading file '{}'", path));
    }
    return evaluate_string(ctx, buffer.str());
}


Object Object::integer(std::string value) {
    errno = 0;
    auto ival = std::strtoimax(value.c_str(), nullptr, 10);
    if (errno != ERANGE)
        return Object::integer(ival);
    mpz_ext big(value);
    return Object::integer(big);
}


std::string Object::type_name() const {
    return std::visit(overloaded {
        [](Null) { return "null"; },
        [](Integer) { return "integer"; },
        [](String) { return "string"; },
        [](Boolean) { return "boolean"; },
        [](Floating) { return "floating"; },
        [](Bignum) { return "integer"; },
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
        [](Bignum) { return Type::integer; },
        [](Map) { return Type::map; },
        [](List) { return Type::list; },
        [](Closure) { return Type::function; },
        [](Builtin) { return Type::function; }
    }, _data);
}


Object Object::operator+(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) {
            auto imin = std::numeric_limits<intmax_t>::max();
            auto imax = std::numeric_limits<intmax_t>::min();
            if (a > 0 && b > 0 && a > imax - b)
                return Object::integer(mpz_ext(a) + mpz_ext(b));
            if (a < 0 && b < 0 && a < imin - b)
                return Object::integer(mpz_ext(a) + mpz_ext(b));
            return Object::integer(a + b);
        },
        [](Integer a, Floating b) { return Object::floating(a + b); },
        [](Floating a, Integer b) { return Object::floating(a + b); },
        [](Floating a, Floating b) { return Object::floating(a + b); },
        [](Integer a, Bignum b) { return Object::integer(mpz_ext(a) + *b).compress(); },
        [](Bignum a, Integer b) { return Object::integer(*a + mpz_ext(b)).compress(); },
        [](Bignum a, Bignum b) { return Object::integer(*a + *b).compress(); },
        [](Floating a, Bignum b) { return Object::floating(a + b->get_d()); },
        [](Bignum a, Floating b) { return Object::floating(a->get_d() + b); },
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
        [](Integer a, Integer b) {
            auto imin = std::numeric_limits<intmax_t>::max();
            auto imax = std::numeric_limits<intmax_t>::min();
            if (a > 0 && b < 0 && a > imax + b)
                return Object::integer(mpz_ext(a) - mpz_ext(b));
            if (a < 0 && b > 0 && a < imin + b)
                return Object::integer(mpz_ext(a) - mpz_ext(b));
            return Object::integer(a - b);
        },
        [](Floating a, Integer b) { return Object::floating(a - b); },
        [](Integer a, Floating b) { return Object::floating(a - b); },
        [](Floating a, Floating b) { return Object::floating(a - b); },
        [](Integer a, Bignum b) { return Object::integer(mpz_ext(a) - *b).compress(); },
        [](Bignum a, Integer b) { return Object::integer(*a - mpz_ext(b)).compress(); },
        [](Bignum a, Bignum b) { return Object::integer(*a - *b).compress(); },
        [](Floating a, Bignum b) { return Object::floating(a - b->get_d()); },
        [](Bignum a, Floating b) { return Object::floating(a->get_d() - b); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `-`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


Object Object::operator-() const {
    return std::visit(overloaded {
        [](Integer x) {
            if (x == std::numeric_limits<std::intmax_t>::min())
                return Object::integer(-mpz_ext(x));
            return Object::integer(-x);
        },
        [](Floating x) { return Object::floating(-x); },
        [](Bignum x) { return Object::integer(-(*x)); },
        [this](auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported type for operator `-`: `{}`",
                type_name()
            ));
        }
    }, _data);
}


Object Object::operator*(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) {
            auto bnd = (intmax_t) sqrt(std::numeric_limits<intmax_t>::max());
            if (a > bnd || -a > bnd || b > bnd || -b > bnd)
                return Object::integer(mpz_ext(a) * mpz_ext(b)).compress();
            return Object::integer(a * b);
        },
        [](Floating a, Integer b) { return Object::floating(a * b); },
        [](Integer a, Floating b) { return Object::floating(a * b); },
        [](Floating a, Floating b) { return Object::floating(a * b); },
        [](Integer a, Bignum b) { return Object::integer(mpz_ext(a) * *b).compress(); },
        [](Bignum a, Integer b) { return Object::integer(*a * mpz_ext(b)).compress(); },
        [](Bignum a, Bignum b) { return Object::integer(*a * *b).compress(); },
        [](Floating a, Bignum b) { return Object::floating(a * b->get_d()); },
        [](Bignum a, Floating b) { return Object::floating(a->get_d() * b); },
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
        [](Integer a, Bignum b) { return Object::floating(a / b->get_d()); },
        [](Bignum a, Integer b) { return Object::floating(a->get_d() / b); },
        [](Bignum a, Bignum b) { return Object::floating(a->get_d() / b->get_d()); },
        [](Floating a, Bignum b) { return Object::floating(a / b->get_d()); },
        [](Bignum a, Floating b) { return Object::floating(a->get_d() / b); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `/`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


Object Object::idiv(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) { return Object::integer(a / b); },
        [](Bignum a, Integer b) { return Object::integer(*a / mpz_ext(b)).compress(); },
        [](Integer a, Bignum b) { return Object::integer(mpz_ext(a) / *b).compress(); },
        [](Bignum a, Bignum b) { return Object::integer(*a / *b).compress(); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `//`: `{}` and `{}`",
                type_name(), other.type_name()
            ));
        }
    }, _data, other._data);
}


Object Object::power(Object other) const {
    return std::visit(overloaded {
        [](Integer a, Integer b) {
            if (b < 0)
                return Object::floating(pow(a, b));
            mpz_ext out, _a(a);
            mpz_pow_ui(out.get_mpz_t(), _a.get_mpz_t(), b);
            return Object::integer(out).compress();
        },
        [](Floating a, Integer b) { return Object::floating(pow(a, b)); },
        [](Integer a, Floating b) { return Object::floating(pow(a, b)); },
        [](Floating a, Floating b) { return Object::floating(pow(a, b)); },
        [](Integer a, Bignum b) { return Object::floating(pow(a, b->get_d())); },
        [](Bignum a, Integer b) {
            if (b < 0)
                return Object::floating(pow(a->get_d(), b));
            mpz_class out;
            mpz_pow_ui(out.get_mpz_t(), a->get_mpz_t(), b);
            return Object::integer(out).compress();
        },
        [](Bignum a, Bignum b) { return Object::floating(pow(a->get_d(), b->get_d())); },
        [](Floating a, Bignum b) { return Object::floating(pow(a, b->get_d())); },
        [](Bignum a, Floating b) { return Object::floating(pow(a->get_d(), b)); },
        [this, other](auto&&, auto&&) -> Object {
            throw EvalException(fmt::format(
                "unsupported types for operator `^`: `{}` and `{}`",
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
        [](Integer a, Bignum b) { mpz_ext _a(a); return mpz_cmp(_a.get_mpz_t(), b->get_mpz_t()) < 0; },
        [](Bignum a, Integer b) { mpz_ext _b(b); return mpz_cmp(a->get_mpz_t(), _b.get_mpz_t()) < 0; },
        [](Bignum a, Bignum b) { return mpz_cmp(a->get_mpz_t(), b->get_mpz_t()) < 0; },
        [](Floating a, Bignum b) { return mpz_cmp_d(b->get_mpz_t(), a) > 0; },
        [](Bignum a, Floating b) { return mpz_cmp_d(a->get_mpz_t(), b) < 0; },
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
        [](Integer a, Bignum b) { mpz_ext _a(a); return mpz_cmp(_a.get_mpz_t(), b->get_mpz_t()) <= 0; },
        [](Bignum a, Integer b) { mpz_ext _b(b); return mpz_cmp(a->get_mpz_t(), _b.get_mpz_t()) <= 0; },
        [](Bignum a, Bignum b) { return mpz_cmp(a->get_mpz_t(), b->get_mpz_t()) <= 0; },
        [](Floating a, Bignum b) { return mpz_cmp_d(b->get_mpz_t(), a) >= 0; },
        [](Bignum a, Floating b) { return mpz_cmp_d(a->get_mpz_t(), b) <= 0; },
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
        [](Integer a, Bignum b) { mpz_ext _a(a); return mpz_cmp(_a.get_mpz_t(), b->get_mpz_t()) > 0; },
        [](Bignum a, Integer b) { mpz_ext _b(b); return mpz_cmp(a->get_mpz_t(), _b.get_mpz_t()) > 0; },
        [](Bignum a, Bignum b) { return mpz_cmp(a->get_mpz_t(), b->get_mpz_t()) > 0; },
        [](Floating a, Bignum b) { return mpz_cmp_d(b->get_mpz_t(), a) < 0; },
        [](Bignum a, Floating b) { return mpz_cmp_d(a->get_mpz_t(), b) > 0; },
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
        [](Integer a, Bignum b) { mpz_ext _a(a); return mpz_cmp(_a.get_mpz_t(), b->get_mpz_t()) >= 0; },
        [](Bignum a, Integer b) { mpz_ext _b(b); return mpz_cmp(a->get_mpz_t(), _b.get_mpz_t()) >= 0; },
        [](Bignum a, Bignum b) { return mpz_cmp(a->get_mpz_t(), b->get_mpz_t()) >= 0; },
        [](Floating a, Bignum b) { return mpz_cmp_d(b->get_mpz_t(), a) <= 0; },
        [](Bignum a, Floating b) { return mpz_cmp_d(a->get_mpz_t(), b) >= 0; },
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
        [](Integer a, Bignum b) { mpz_ext _a(a); return mpz_cmp(_a.get_mpz_t(), b->get_mpz_t()) == 0; },
        [](Bignum a, Integer b) { mpz_ext _b(b); return mpz_cmp(a->get_mpz_t(), _b.get_mpz_t()) == 0; },
        [](Bignum a, Bignum b) { return mpz_cmp(a->get_mpz_t(), b->get_mpz_t()) == 0; },
        [](Floating a, Bignum b) { return mpz_cmp_d(b->get_mpz_t(), a) == 0; },
        [](Bignum a, Floating b) { return mpz_cmp_d(a->get_mpz_t(), b) == 0; },
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


Object Object::call(EvaluationContext& ctx, const Object& args, const Object& kwargs) const {
    return std::visit(overloaded {
        [&ctx, &args, &kwargs](Closure c) -> Object {
            ForwardContext newctx(ctx);
            newctx.push_namespace(c->nonlocals);
            newctx.push_namespace();
            if (!c->args->bind(newctx, args))
                throw EvalException(c->args->src, "failed to bind pattern");
            if (!c->kwargs->bind(newctx, kwargs))
                throw EvalException(c->kwargs->src, "failed to bind pattern");
            return c->expression->evaluate(newctx);
        },
        [&ctx, &args](Builtin b) -> Object {
            return b.callable(ctx, args);
        },
        [this](auto&&) -> Object {
            throw EvalException(fmt::format("attempted to call non-function: `{}`", type_name()));
        }
    }, _data);
}


Object Object::call(EvaluationContext& ctx, const Object& args) const {
    return call(ctx, args, Object::map());
}


Object Object::call(EvaluationContext& ctx, const std::vector<Object>& args) const {
    return call(ctx, Object::list(args));
}


Object Object::call(const std::vector<Object>& args) const {
    EvaluationContext ctx;
    return call(ctx, Object::list(args));
}


Object Object::call(const Object& args) const {
    EvaluationContext ctx;
    return call(ctx, args);
}


Object Object::call(const Object& args, const Object& kwargs) const {
    EvaluationContext ctx;
    return call(ctx, args, kwargs);
}


Object Object::operator[](Object index) const {
    return std::visit(overloaded {
        [this](Integer x) { return (*this)[x]; },
        [this](Bignum x) -> Object {
            // Small bignums should never exist
            throw EvalException(fmt::format("index out of bounds: {}", x->get_str()));
        },
        [this](String x) { return (*this)[x]; },
        [&index](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported subscript type: `{}`", index.type_name()));
        }
    }, index._data);
}


Object Object::operator[](intmax_t index) const {
    return std::visit(overloaded {
        [index](List list) {
            if (index < 0 || (size_t)index >= list->size())
                throw EvalException(fmt::format("list index out of range: {}", index));
            return (*list)[index];
        },
        [this](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for integer subscripting: `{}`", type_name()));
        }
    }, _data);
}


Object Object::operator[](std::string index) const {
    return std::visit(overloaded {
        [index](Map map) {
            if (map->find(index) == map->end())
                throw EvalException(fmt::format("key not found: {}", index));
            return (*map)[index];
        },
        [this](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for string subscripting: `{}`", type_name()));
        }
    }, _data);
}


Object::operator bool() const {
    return std::visit(overloaded {
        [](Null x) { return false; },
        [](Boolean x) { return x; },
        [](auto&&) { return true; }
    }, _data);
}


Object Object::compress() const {
    return std::visit(overloaded {
        [this](Bignum x) -> Object {
            if (x->fits_intmax_t())
                return Object::integer(x->get_intmax_t());
            return *this;
        },
        [this](auto&&) { return *this; }
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


std::string Object::dump()const {
    std::ostringstream os;
    dump(os);
    return os.str();
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
        [&os](Bignum x) { os << x->get_str(); },
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


const char* EvalException::what() const noexcept {
    if (message.has_value())
        return message.value().c_str();

    std::ostringstream msg;
    msg << reason;
    for (size_t i = 0; i < positions.size(); i++) {
        std::string src = fmt::format("at {}:{}", positions[i].line, positions[i].column);
        msg << std::endl << src;
        if (i >= lines.size())
            continue;
        msg << ": " << lines[i] << std::endl;
        for (std::size_t j = 1; j < src.size() + positions[i].column + 2; j++)
            msg << "-";
        msg << "^";
    }
    const_cast<EvalException*>(this)->message = msg.str();
    return message.value().c_str();
}


void EvalException::tag_position(Source source, bool always_add) noexcept {
    if (always_add)
        positions.push_back(source);
    else if (positions.empty())
        positions.push_back(source);
}


void EvalException::tag_lines(std::function<std::string_view(Source&)> func) noexcept {
    lines.clear();
    for (auto& pos : positions)
        lines.emplace_back(func(pos));
}


static uptr<std::vector<uptr<LibFinder>>> _stdlibs = nullptr;

std::vector<uptr<LibFinder>>& stdlibs() {
    if (!_stdlibs)
        _stdlibs = std::make_unique<std::vector<uptr<LibFinder>>>();
    return *_stdlibs;
}

void Gold::register_stdlib(uptr<LibFinder> finder) {
    stdlibs().push_back(std::move(finder));
}


Object EvaluationContext::import(const std::string& path) {
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

    return evaluate_file(*this, path);
}


Object EvaluationContext::lookup(const std::string& key) {
    auto val = weak_lookup(key);
    if (!val.has_value())
        throw EvalException(fmt::format("unbound name: `{}`", key));
    return val.value();
}


opt<Object> EvaluationContext::weak_lookup(const std::string& key) {
    for (auto& ns : namespaces) {
        if (ns.find(key) == ns.end())
            continue;
        return ns[key];
    }
    return opt<Object>();
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


static Object builtin_int(EvaluationContext&, const Object& args) {
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


static Object builtin_bool(EvaluationContext&, const Object& args) {
    return Object::boolean((bool)args[0]);
}


static Object builtin_str(EvaluationContext&, const Object& args) {
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


static Object builtin_float(EvaluationContext&, const Object& args) {
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


static Object builtin_len(EvaluationContext&, const Object& args) {
    Object arg = args[0];
    return std::visit(overloaded {
        [](Object::List x) { return Object::integer(x->size()); },
        [](Object::Map x) { return Object::integer(x->size()); },
        [&arg](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `len()`: `{}`", arg.type_name()));
        }
    }, arg.data());
}


static Object builtin_range(EvaluationContext&, const Object& args) {
    std::for_each(args.unsafe_list()->begin(), args.unsafe_list()->end(), [](auto x) {
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


static Object builtin_map(EvaluationContext& ctx, const Object& args) {
    Object func = args[0];
    Object sequence = args[1];
    return std::visit(overloaded {
        [&func, &ctx](Object::List x) {
            auto result = std::make_shared<Object::ListT>();
            result->resize(x->size());
            std::transform(
                x->begin(), x->end(), result->begin(),
                [&func, &ctx](Object x) { return func(ctx, x); }
            );
            return Object::list(result);
        },
        [&sequence](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `map()`: `{}`", sequence.type_name()));
        }
    }, sequence.data());
}


static Object builtin_filter(EvaluationContext& ctx, const Object& args) {
    Object func = args[0];
    Object sequence = args[1];
    return std::visit(overloaded {
        [&func, &ctx](Object::List x) {
            auto result = std::make_shared<Object::ListT>();
            std::copy_if(
                x->begin(), x->end(), std::back_inserter(*result),
                [&func, &ctx](auto x) { return (bool)func(ctx, x); }
            );
            return Object::list(result);
        },
        [&sequence](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `filter()`: `{}`", sequence.type_name()));
        }
    }, sequence.data());
}


static Object builtin_items(EvaluationContext& ctx, const Object& args) {
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
            throw EvalException(fmt::format("unsupported type for `items()`: `{}`", map.type_name()));
        }
    }, map.data());
}


static Object builtin_exp(EvaluationContext& ctx, const Object& args) {
    double logbase = 1.0;
    if (args.size() > 1)
        logbase = log(std::visit(overloaded {
            [](Object::Integer x) -> double { return x; },
            [](Object::Floating x) { return x; },
            [&args](auto&&) -> double {
                throw EvalException(fmt::format("unsupported type for exponent: `{}`", args[1].type_name()));
            }
        }, args[1].data()));

    return std::visit(overloaded {
        [logbase](Object::Integer x) { return Object::floating(exp(x * logbase)); },
        [logbase](Object::Floating x) { return Object::floating(exp(x * logbase)); },
        [&args](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for base: `{}`", args[0].type_name()));
        }
    }, args[0].data());
}


static Object builtin_log(EvaluationContext& ctx, const Object& args) {
    double logbase = 1.0;
    if (args.size() > 1)
        logbase = log(std::visit(overloaded {
            [](Object::Integer x) -> double { return x; },
            [](Object::Floating x) { return x; },
            [&args](auto&&) -> double {
                throw EvalException(fmt::format("unsupported type for exponent: `{}`", args[1].type_name()));
            }
        }, args[1].data()));

    return std::visit(overloaded {
        [logbase](Object::Integer x) { return Object::floating(log(x) / logbase); },
        [logbase](Object::Floating x) { return Object::floating(log(x) / logbase); },
        [&args](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for base: `{}`", args[0].type_name()));
        }
    }, args[0].data());
}


static Object builtin_ord(EvaluationContext& ctx, const Object& args) {
    return std::visit(overloaded {
        [](Object::String x) {
            if (x.size() != 1)
                throw EvalException("string must have length 1");
            return Object::integer(x[0]);
        },
        [&args](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `ord()`: `{}`", args[0].type_name()));
        }
    }, args[0].data());
}


static Object builtin_chr(EvaluationContext& ctx, const Object& args) {
    return std::visit(overloaded {
        [](Object::Integer x) { return Object::string(std::string {(char)x}); },
        [&args](auto&&) -> Object {
            throw EvalException(fmt::format("unsupported type for `chr()`: `{}`", args[0].type_name()));
        }
    }, args[0].data());
}


static Object builtin_isint(EvaluationContext& ctx, const Object& args) {
    return Object::boolean(args[0].type() == Object::Type::integer);
}


static Object builtin_isstr(EvaluationContext& ctx, const Object& args) {
    return Object::boolean(args[0].type() == Object::Type::string);
}


static Object builtin_isnull(EvaluationContext& ctx, const Object& args) {
    return Object::boolean(args[0].type() == Object::Type::null);
}


static Object builtin_isbool(EvaluationContext& ctx, const Object& args) {
    return Object::boolean(args[0].type() == Object::Type::boolean);
}


static Object builtin_isfloat(EvaluationContext& ctx, const Object& args) {
    return Object::boolean(args[0].type() == Object::Type::floating);
}


static Object builtin_isobject(EvaluationContext& ctx, const Object& args) {
    return Object::boolean(args[0].type() == Object::Type::map);
}


static Object builtin_islist(EvaluationContext& ctx, const Object& args) {
    return Object::boolean(args[0].type() == Object::Type::list);
}


static Object builtin_isfunc(EvaluationContext& ctx, const Object& args) {
    return Object::boolean(args[0].type() == Object::Type::function);
}


static Object builtin_import(EvaluationContext& ctx, const Object& args) {
    Object arg = args[0];
    if (arg.type() != Object::Type::string)
        throw EvalException(fmt::format("unsupported type for `import()`: `{}`", arg.type_name()));
    return ctx.import(arg.unsafe_string());
}


#define BUILTIN(x) { #x, Object(Object::Builtin { #x, builtin_##x })}


Namespace Gold::builtins = {
    BUILTIN(int),
    BUILTIN(bool),
    BUILTIN(str),
    BUILTIN(float),
    BUILTIN(len),
    BUILTIN(range),
    BUILTIN(map),
    BUILTIN(filter),
    BUILTIN(items),
    BUILTIN(exp),
    BUILTIN(log),
    BUILTIN(ord),
    BUILTIN(chr),
    BUILTIN(isint),
    BUILTIN(isstr),
    BUILTIN(isnull),
    BUILTIN(isbool),
    BUILTIN(isfloat),
    BUILTIN(isobject),
    BUILTIN(islist),
    BUILTIN(isfunc),
    BUILTIN(import),
};
