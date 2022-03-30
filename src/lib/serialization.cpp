#include <fmt/core.h>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


std::string Serializable::serialize() const {
    std::ostringstream os;
    serialize(os);
    return os.str();
}


void Serializable::serialize(std::ostream& os) const {
    Serializer s(os);
    serialize(s);
}


void Serializable::serialize(Serializer& s) const {
    do_serialize(s);
}


Serializer& Serializer::operator<<(const std::string& str) {
    auto size = str.size();
    *this << size;
    os.write(str.c_str(), size);
    return *this;
}


void Deserializer::readref(std::string& str) {
    size_t size = read<size_t>();
    char* data = new char[size];
    is.read(data, size);
    str.assign(data, size);
    delete[] data;
}


void Object::do_serialize(Serializer& s) const {
    std::visit(overloaded {
        [&s](Object::Null) { s << 'N'; },
        [&s](Object::Integer v) { s << 'I' << v; },
        [&s](Object::String v) { s << 'S' << v; },
        [&s](Object::Boolean v) { s << 'B' << v; },
        [&s](Object::Floating v) { s << 'F' << v; },
        [&s](Object::Map v) { s << 'M' << v; },
        [&s](Object::List v) { s << 'L' << v; },
        [&s](Object::Closure v) {
            s << 'C';
            s.write(v, [&s](Object::ClosureT& c) {
                s << c.nonlocals << c.args << c.kwargs << c.expression;
            });
        },
        [&s](Object::Builtin v) { s << 'U' << v.name; }
    }, data());
}


Object Object::deserialize(Deserializer& is) {
    char indicator = is.read<char>();
    switch (indicator) {
    case 'N': return Object::null();
    case 'I': return Object::integer(is.read<Object::Integer>());
    case 'S': return Object::string(is.read<Object::String>());
    case 'B': return Object::boolean(is.read<Object::Boolean>());
    case 'F': return Object::floating(is.read<Object::Floating>());
    case 'M': return Object::map(is.read<Object::Map>([&is]() {
        return is.read<Object::MapT*>([&is]() {
            auto key = is.read<std::string>();
            auto value = Object::deserialize(is);
            return std::pair<std::string, Object> { key, value };
        });
    }));
    case 'L': return Object::list(is.read<Object::List>([&is]() {
        return is.read<Object::ListT*>([&is]() {
            return Object::deserialize(is);
        });
    }));
    case 'C': {
        return Object::closure(is.read<Object::Closure>([&is]() {
            auto closure = new Object::ClosureT;
            closure->nonlocals = is.read<std::map<std::string, Object>>([&is]() {
                auto key = is.read<std::string>();
                auto value = Object::deserialize(is);
                return std::pair(key, value);
            });
            closure->args = is.read<sptr<Binding>>([&is]() {
                return Binding::deserialize(is).release();
            });
            closure->kwargs = is.read<sptr<Binding>>([&is]() {
                return Binding::deserialize(is).release();
            });
            closure->expression = is.read<sptr<Expr>>([&is]() {
                return Expr::deserialize(is).release();
            });
            return closure;
        }));
    }
    case 'U': return builtins[is.read<std::string>()];
    }

    throw InternalException(fmt::format("unknown object indicator: {}", (int)indicator));
}


Object Object::deserialize(std::string val) {
    std::istringstream is(val);
    return deserialize(is);
}


Object Object::deserialize(std::istream& is) {
    Deserializer d(is);
    return deserialize(d);
}


BindingPtr Binding::deserialize(Deserializer& is) {
    auto indicator = is.read<char>();
    auto src = is.read<Source>();
    switch (indicator) {
    case 'I':
        return std::make_unique<IdentifierBinding>(src, is.read<std::string>());
    case 'L': {
        auto bindings = is.read<std::vector<ListBinding::Entry>>([&is]() {
            auto binding = Binding::deserialize(is);
            auto fallback = is.read<opt<ExprPtr>>([&is]() { return Expr::deserialize(is); });
            return ListBinding::Entry { std::move(binding), std::move(fallback) };
        });
        auto slurp = is.read<bool>();
        auto slurp_target = is.read<opt<std::string>>();
        return std::make_unique<ListBinding>(src, std::move(bindings), slurp, slurp_target);
    }
    case 'M': {
        auto entries = is.read<std::vector<MapBinding::Entry>>([&is]() {
            auto name = is.read<std::string>();
            auto binding = Binding::deserialize(is);
            auto fallback = is.read<opt<ExprPtr>>([&is]() { return Expr::deserialize(is); });
            return MapBinding::Entry { name, std::move(binding), std::move(fallback) };
        });
        auto slurp_target = is.read<opt<std::string>>();
        return std::make_unique<MapBinding>(src, std::move(entries), slurp_target);
    }
    default:
        throw InternalException(fmt::format("unknown binding indicator: {}", (int)indicator));
    }
}


void IdentifierBinding::do_serialize(Serializer& os) const {
    os << 'I' << src << name;
}


void ListBinding::do_serialize(Serializer& os) const {
    os << 'L' << src;
    os.write(bindings, [&os](const ListBinding::Entry& entry) {
        os << entry.binding << entry.fallback;
    });
    os << slurp << slurp_target;
}


void MapBinding::do_serialize(Serializer& os) const {
    os << 'M' << src;
    os.write(entries, [&os](const MapBinding::Entry& entry) {
        os << entry.name << entry.binding << entry.fallback;
    });
    os << slurp_target;
}


void Literal::do_serialize(Serializer& os) const {
    os << 'T' << source() << object;
}


void Identifier::do_serialize(Serializer& os) const {
    os << 'I' << source() << name;
}


void List::do_serialize(Serializer& os) const {
    os << 'L' << source() << elements;
}


void Map::do_serialize(Serializer& os) const {
    os << 'M' << source() << elements;
}


void BinOp::do_serialize(Serializer& os) const {
    os << 'O' << source() << lhs << rhs << op;
}


void UnOp::do_serialize(Serializer& os) const {
    os << 'U' << source() << operand << op;
}


void Block::do_serialize(Serializer& os) const {
    os << 'B' << source();
    os.write(bindings, [&os](const BindingElement& binding) {
        os << binding.binding << binding.expression;
    });
    os << expression;
}


void Function::do_serialize(Serializer& os) const {
    os << 'F' << source() << *args << *kwargs << *expression;
}


void Branch::do_serialize(Serializer& os) const {
    os << 'C' << source() << condition << if_value << else_value;
}


void FunCall::do_serialize(Serializer& os) const {
    os << 'E' << source() << function << args;
    os.write(kwargs, [&os](const std::pair<std::string, ExprPtr>& pair) {
        os << pair.first << pair.second;
    });
}


void Index::do_serialize(Serializer& os) const {
    os << 'S' << source() << haystack << needle;
}


ExprPtr Expr::deserialize(std::string val) {
    std::istringstream is(val);
    return deserialize(is);
}


ExprPtr Expr::deserialize(std::istream& is) {
    Deserializer d(is);
    return deserialize(d);
}


ExprPtr Expr::deserialize(Deserializer& is) {
    auto indicator = is.read<char>();
    auto source = is.read<Source>();
    switch (indicator) {
    case 'T':
        return std::make_unique<Literal>(source, Object::deserialize(is));
    case 'I':
        return std::make_unique<Identifier>(source, is.read<std::string>());
    case 'L': {
        auto elements = is.read<std::vector<uptr<CollectionElement>>>([&is]() {
            return CollectionElement::deserialize(is);
        });
        return std::make_unique<List>(source, std::move(elements));
    }
    case 'M': {
        auto entries = is.read<std::vector<uptr<CollectionElement>>>([&is]() {
            return CollectionElement::deserialize(is);
        });
        return std::make_unique<Map>(source, std::move(entries));
    }
    case 'O': {
        auto lhs = Expr::deserialize(is);
        auto rhs = Expr::deserialize(is);
        auto op = is.read<BinaryOperator>();
        return std::make_unique<BinOp>(source, std::move(lhs), std::move(rhs), op);
    }
    case 'U': {
        auto operand = Expr::deserialize(is);
        auto op = is.read<UnaryOperator>();
        return std::make_unique<UnOp>(source, std::move(operand), op);
    }
    case 'B': {
        auto bindings = is.read<std::vector<Block::BindingElement>>([&is]() {
            auto binding = Binding::deserialize(is);
            auto subnode = Expr::deserialize(is);
            return Block::BindingElement {std::move(binding), std::move(subnode)};
        });
        return std::make_unique<Block>(source, std::move(bindings), Expr::deserialize(is));
    }
    case 'F': {
        auto args = Binding::deserialize(is);
        auto kwargs = Binding::deserialize(is);
        auto expression = Expr::deserialize(is);
        return std::make_unique<Function>(source, std::move(args), std::move(kwargs), std::move(expression));
    }
    case 'C': {
        auto cond = Expr::deserialize(is);
        auto yes = Expr::deserialize(is);
        auto no = Expr::deserialize(is);
        return std::make_unique<Branch>(source, std::move(cond), std::move(yes), std::move(no));
    }
    case 'E': {
        auto func = Expr::deserialize(is);
        auto args = is.read<std::vector<ExprPtr>>([&is]() {
            return Expr::deserialize(is);
        });
        auto kwargs = is.read<std::vector<std::pair<std::string, ExprPtr>>>([&is]() {
            auto key = is.read<std::string>();
            auto expr = Expr::deserialize(is);
            return std::make_pair(key, std::move(expr));
        });
        return std::make_unique<FunCall>(source, std::move(func), std::move(args), std::move(kwargs));
    }
    case 'S': {
        auto haystack = Expr::deserialize(is);
        auto needle = Expr::deserialize(is);
        return std::make_unique<Index>(source, std::move(haystack), std::move(needle));
    }
    default:
        throw InternalException(fmt::format("unknown AST indicator: {}", (int)indicator));
    }
}


uptr<CollectionElement> CollectionElement::deserialize(Deserializer& is) {
    auto indicator = is.read<char>();
    switch (indicator) {
    case 'S': return std::make_unique<SplatElement>(Expr::deserialize(is));
    case 'E': return std::make_unique<SingletonListElement>(Expr::deserialize(is));
    case 'C': {
        auto cond = Expr::deserialize(is);
        auto element = ListElement::deserialize(is);
        return std::make_unique<CondListElement>(std::move(cond), std::move(element));
    }
    case 'L': {
        auto binding = Binding::deserialize(is);
        auto iter = Expr::deserialize(is);
        auto element = ListElement::deserialize(is);
        return std::make_unique<LoopListElement>(std::move(binding), std::move(iter), std::move(element));
    }
    case 'e': {
        auto key = Expr::deserialize(is);
        auto node = Expr::deserialize(is);
        return std::make_unique<SingletonMapElement>(std::move(key), std::move(node));
    }
    case 'c': {
        auto cond = Expr::deserialize(is);
        auto element = MapElement::deserialize(is);
        return std::make_unique<CondMapElement>(std::move(cond), std::move(element));
    }
    case 'l': {
        auto binding = Binding::deserialize(is);
        auto iter = Expr::deserialize(is);
        auto element = MapElement::deserialize(is);
        return std::make_unique<LoopMapElement>(std::move(binding), std::move(iter), std::move(element));
    }
    default:
        throw InternalException(fmt::format("unknown collection element indicator: {}", (int)indicator));
    }
}


void SplatElement::do_serialize(Serializer& os) const {
    os << 'S' << node;
}


void SingletonListElement::do_serialize(Serializer& os) const {
    os << 'E' << node;
}


void CondListElement::do_serialize(Serializer& os) const {
    os << 'C' << cond << element;
}


void LoopListElement::do_serialize(Serializer& os) const {
    os << 'L' << binding << iter << element;
}


void SingletonMapElement::do_serialize(Serializer& os) const {
    os << 'e' << key << node;
}


void CondMapElement::do_serialize(Serializer& os) const {
    os << 'c' << cond << element;
}


void LoopMapElement::do_serialize(Serializer& os) const {
    os << 'l' << binding << iter << element;
}
