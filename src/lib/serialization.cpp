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
    case 'M': obj = Object::map(read<std::map<std::string, Object>>()); return;
    case 'L': obj = Object::list(read<std::vector<Object>>()); return;
    case 'C': {
        auto closure = std::make_shared<Object::ClosureT>();
        closure->nonlocals = read<std::map<std::string, Object>>();
        closure->parameters = std::make_shared<std::vector<std::string>>(read<std::vector<std::string>>());
        closure->expression = read<AstPtr>();
        obj = Object::closure(closure);
        return;
    }
    case 'U': obj = builtins[read<std::string>()]; return;
    }

    throw InternalException();
}


Serializer& Serializer::operator<<(const AstNode& node) {
    node.serialize(*this);
    return *this;
}


void Deserializer::readref(AstPtr& node) {
    node = AstNode::deserialize(*this);
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
        os << *entry.node << entry.splat;
    });
}


void Map::serialize(Serializer& os) const {
    os << 'M' << source();
    os.write(entries, [&os](const Entry& entry) {
        os << entry.key << *entry.node << entry.splat;
    });
}


void BinOp::serialize(Serializer& os) const {
    os << 'O' << source() << *lhs << *rhs << op;
}


void Block::serialize(Serializer& os) const {
    os << 'B' << source();
    os.write(bindings, [&os](const std::pair<std::string, AstPtr>& entry) {
        os << entry.first << *entry.second;
    });
    os << *expression;
}


void Function::serialize(Serializer& os) const {
    os << 'F' << source() << *parameters << *expression;
}


void Branch::serialize(Serializer& os) const {
    os << 'C' << source() << *condition << *if_value << *else_value;
}


void FunCall::serialize(Serializer& os) const {
    os << 'E' << source() << *function << args;
}


void Index::serialize(Serializer& os) const {
    os << 'S' << source() << *haystack << *needle;
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
    auto indicator = is.read<char>();
    auto source = is.read<Source>();
    switch (indicator) {
    case 'T': {
        auto node = Literal {{source}, is.read<Object>()};
        return std::make_unique<Literal>(node);
    }
    case 'I': {
        auto node = Identifier {{source}, is.read<std::string>()};
        return std::make_unique<Identifier>(node);
    }
    case 'L': {
        auto elements = is.read<std::vector<List::Entry>>([&is]() {
            return List::Entry {
                is.read<AstPtr>(),
                is.read<bool>()
            };
        });
        auto node = List {{source}, std::move(elements)};
        return std::make_unique<List>(std::move(node));
    }
    case 'M': {
        auto entries = is.read<std::vector<Map::Entry>>([&is]() {
            return Map::Entry {
                is.read<std::string>(),
                is.read<AstPtr>(),
                is.read<bool>()
            };
        });
        auto node = Map {{source}, std::move(entries)};
        return std::make_unique<Map>(std::move(node));
    }
    case 'O': {
        auto node = BinOp {
            {source},
            is.read<AstPtr>(),
            is.read<AstPtr>(),
            is.read<Operator>()
        };
        return std::make_unique<BinOp>(std::move(node));
    }
    case 'B': {
        auto bindings = is.read<std::vector<std::pair<std::string, AstPtr>>>([&is]() {
            return std::pair<std::string, AstPtr> {
                is.read<std::string>(),
                is.read<AstPtr>()
            };
        });
        auto node = Block {
            {source},
            std::move(bindings),
            is.read<AstPtr>()
        };
        return std::make_unique<Block>(std::move(node));
    }
    case 'F': {
        auto node = Function {
            {source},
            std::make_shared<std::vector<std::string>>(is.read<std::vector<std::string>>()),
            is.read<AstPtr>()
        };
        return std::make_unique<Function>(std::move(node));
    }
    case 'C': {
        auto node = Branch {
            {source},
            is.read<AstPtr>(),
            is.read<AstPtr>(),
            is.read<AstPtr>()
        };
        return std::make_unique<Branch>(std::move(node));
    }
    case 'E': {
        auto node = FunCall {
            {source},
            is.read<AstPtr>(),
            is.read<std::vector<AstPtr>>(),
        };
        return std::make_unique<FunCall>(std::move(node));
    }
    case 'S': {
        auto node = Index {
            {source},
            is.read<AstPtr>(),
            is.read<AstPtr>()
        };
        return std::make_unique<Index>(std::move(node));
    }
    default:
        throw InternalException();
    }
}
