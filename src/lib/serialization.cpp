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
    os << 'L' << source() << elements.size();
    for (auto& entry : elements)
        os << *entry.node << entry.splat;
}


void Map::serialize(Serializer& os) const {
    os << 'M' << source() << entries.size();
    for (auto& entry : entries)
        os << entry.key << *entry.node << entry.splat;
}


void BinOp::serialize(Serializer& os) const {
    os << 'O' << source() << *lhs << op << *rhs;
}


void Block::serialize(Serializer& os) const {
    os << 'B' << source() << bindings.size();
    for (auto& [key, value] : bindings)
        os << key << *value;
    os << *expression;
}


void Function::serialize(Serializer& os) const {
    os << 'F' << source() << parameters->size();
    for (auto& p : *parameters)
        os << p;
    os << *expression;
}


void Branch::serialize(Serializer& os) const {
    os << 'C' << source() << *condition << *if_value << *else_value;
}


void FunCall::serialize(Serializer& os) const {
    os << 'E' << source() << *function << args.size();
    for (auto& arg : args)
        os << *arg;
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
    case 'T':
        return std::make_unique<Literal>(source, is.read<Object>());
    case 'I':
        return std::make_unique<Identifier>(source, is.read<std::string>());
    case 'L': {
        auto list = std::make_unique<List>(source);
        auto size = is.read<size_t>();
        for (size_t i = 0; i < size; i++) {
            auto node = is.read<AstPtr>();
            list->append(std::move(node), is.read<bool>());
        }
        return list;
    }
    case 'M': {
        auto map = std::make_unique<Map>(source);
        auto size = is.read<size_t>();
        for (size_t i = 0; i < size; i++) {
            auto key = is.read<std::string>();
            auto value = is.read<AstPtr>();
            auto splat = is.read<bool>();
            map->append(key, std::move(value), splat);
        }
        return map;
    }
    case 'O': {
        auto lhs = AstNode::deserialize(is);
        auto op = is.read<Operator>();
        auto rhs = is.read<AstPtr>();
        return std::make_unique<BinOp>(source, std::move(lhs), std::move(rhs), op);
    }
    case 'B': {
        auto block = std::make_unique<Block>(source);
        auto size = is.read<size_t>();
        for (size_t i = 0; i < size; i++) {
            auto key = is.read<std::string>();
            auto value = is.read<AstPtr>();
            block->append(key, std::move(value));
        }
        block->set_expression(is.read<AstPtr>());
        return block;
    }
    case 'F': {
        auto func = std::make_unique<Function>(source);
        auto size = is.read<size_t>();
        for (size_t i = 0; i < size; i++)
            func->append(is.read<std::string>());
        func->set_expression(is.read<AstPtr>());
        return func;
    }
    case 'C': {
        auto cond = is.read<AstPtr>();
        auto yes = is.read<AstPtr>();
        auto no = is.read<AstPtr>();
        return std::make_unique<Branch>(source, std::move(cond), std::move(yes), std::move(no));
    }
    case 'E': {
        auto call = std::make_unique<FunCall>(source, AstNode::deserialize(is));
        auto size = is.read<size_t>();
        for (size_t i = 0; i < size; i++)
            call->append(is.read<AstPtr>());
        return call;
    }
    case 'S': {
        auto container = is.read<AstPtr>();
        auto index = is.read<AstPtr>();
        return std::make_unique<Index>(source, std::move(container), std::move(index));
    }
    default:
        throw InternalException();
    }
}
