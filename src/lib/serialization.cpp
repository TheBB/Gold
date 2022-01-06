#include <fmt/core.h>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


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


Serializer& Serializer::operator<<(const Object& obj) {
    Serializer& s = *this;
    std::visit(overloaded {
        [&s](Object::Null) { s << 'N'; },
        [&s](Object::Integer v) { s << 'I' << v; },
        [&s](Object::String v) { s << 'S' << v; },
        [&s](Object::Boolean v) { s << 'B' << v; },
        [&s](Object::Floating v) { s << 'F' << v; },
        [&s](Object::Map v) { s << 'M' << v; },
        [&s](Object::List v) { s << 'L' << v; },
        [&s](Object::Closure v) { s << 'C' << v->nonlocals << v->parameters << v->expression; },
        [&s](Object::Builtin v) { s << 'U' << v.name; }
    }, obj.data());
    return *this;
}


void Deserializer::readref(Object& obj) {
    char indicator = read<char>();
    switch (indicator) {
    case 'N': obj = Object::null(); return;
    case 'I': obj = Object::integer(read<Object::Integer>()); return;
    case 'S': obj = Object::string(read<Object::String>()); return;
    case 'B': obj = Object::boolean(read<Object::Boolean>()); return;
    case 'F': obj = Object::floating(read<Object::Floating>()); return;
    case 'M': obj = Object::map(read<Object::Map>()); return;
    case 'L': obj = Object::list(read<Object::List>()); return;
    case 'C': {
        auto closure = std::make_shared<Object::ClosureT>();
        closure->nonlocals = read<std::map<std::string, Object>>();
        closure->parameters = read<std::shared_ptr<std::vector<std::string>>>();
        closure->expression = read<AstPtr>();
        obj = Object::closure(closure);
        return;
    }
    case 'U': obj = builtins[read<std::string>()]; return;
    }

    throw InternalException(fmt::format("unknown object indicator: {}", (int)indicator));
}


Serializer& Serializer::operator<<(const AstNode& node) {
    node.serialize(*this);
    return *this;
}


void Deserializer::readref(AstNode*& node) {
    node = AstNode::deserialize_raw(*this);
}


std::string Object::serialize() const {
    std::ostringstream os;
    serialize(os);
    return os.str();
}


void Object::serialize(std::ostream& os) const {
    Serializer(os) << *this;
}


Object Object::deserialize(std::string val) {
    std::istringstream is(val);
    return deserialize(is);
}


Object Object::deserialize(std::istream& is) {
    return Deserializer(is).read<Object>();
}


std::string AstNode::serialize() const {
    std::ostringstream os;
    serialize(os);
    return os.str();
}


void AstNode::serialize(std::ostream& os) const {
    Serializer(os) << *this;
}


void Literal::serialize(Serializer& os) const {
    os << 'T' << source() << object;
}


void Identifier::serialize(Serializer& os) const {
    os << 'I' << source() << name;
}


void List::serialize(Serializer& os) const {
    os << 'L' << source();
    os.write(elements, [&os](const Entry& entry) {
        os << entry.node << entry.splat;
    });
}


void Map::serialize(Serializer& os) const {
    os << 'M' << source();
    os.write(entries, [&os](const Entry& entry) {
        os << entry.key << entry.node << entry.splat;
    });
}


void BinOp::serialize(Serializer& os) const {
    os << 'O' << source() << lhs << rhs << op;
}


void Block::serialize(Serializer& os) const {
    os << 'B' << source();
    os.write(bindings, [&os](const Binding& binding) {
        os << binding.name << binding.expression;
    });
    os << expression;
}


void Function::serialize(Serializer& os) const {
    os << 'F' << source() << parameters << *expression;
}


void Branch::serialize(Serializer& os) const {
    os << 'C' << source() << condition << if_value << else_value;
}


void FunCall::serialize(Serializer& os) const {
    os << 'E' << source() << function << args;
}


void Index::serialize(Serializer& os) const {
    os << 'S' << source() << haystack << needle;
}


AstPtr AstNode::deserialize(std::string val) {
    std::istringstream is(val);
    return deserialize(is);
}


AstPtr AstNode::deserialize(std::istream& is) {
    Deserializer d(is);
    return deserialize(d);
}


AstPtr AstNode::deserialize(Deserializer& is) {
    return is.read<AstPtr>();
}


AstNode* AstNode::deserialize_raw(Deserializer& is) {
    auto indicator = is.read<char>();
    auto source = is.read<Source>();
    switch (indicator) {
    case 'T':
        return new Literal {{source}, is.read<Object>()};
    case 'I':
        return new Identifier {{source}, is.read<std::string>()};
    case 'L': {
        auto elements = is.read<std::vector<List::Entry>>([&is]() {
            auto subnode = is.read<AstPtr>();
            auto splat = is.read<bool>();
            return List::Entry {std::move(subnode), splat};
        });
        return new List {{source}, std::move(elements)};
    }
    case 'M': {
        auto entries = is.read<std::vector<Map::Entry>>([&is]() {
            auto name = is.read<std::string>();
            auto subnode = is.read<AstPtr>();
            auto splat = is.read<bool>();
            return Map::Entry {name, std::move(subnode), splat};
        });
        return new Map {{source}, std::move(entries)};
    }
    case 'O': {
        auto lhs = is.read<AstPtr>();
        auto rhs = is.read<AstPtr>();
        auto op = is.read<Operator>();
        return new BinOp {{source}, std::move(lhs), std::move(rhs), op};
    }
    case 'B': {
        auto bindings = is.read<std::vector<Block::Binding>>([&is]() {
            auto name = is.read<std::string>();
            auto subnode = is.read<AstPtr>();
            return Block::Binding {name, std::move(subnode)};
        });
        return new Block {{source}, std::move(bindings), is.read<AstPtr>()};
    }
    case 'F': {
        auto parameters = is.read<std::shared_ptr<std::vector<std::string>>>();
        auto expression = is.read<AstPtr>();
        return new Function {
            {source},
            parameters,
            std::move(expression)
        };
    }
    case 'C': {
        auto cond = is.read<AstPtr>();
        auto yes = is.read<AstPtr>();
        auto no = is.read<AstPtr>();
        return new Branch {{source}, std::move(cond), std::move(yes), std::move(no)};
    }
    case 'E': {
        auto func = is.read<AstPtr>();
        auto args = is.read<std::vector<AstPtr>>();
        return new FunCall {{source}, std::move(func), std::move(args)};
    }
    case 'S': {
        auto haystack = is.read<AstPtr>();
        auto needle = is.read<AstPtr>();
        return new Index {{source}, std::move(haystack), std::move(needle)};
    }
    default:
        throw InternalException(fmt::format("unknown AST indicator: {}", (int)indicator));
    }
}
