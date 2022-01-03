#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


std::string Object::serialize() const {
    std::ostringstream os;
    serialize(os);
    return os.str();
}


template <typename T>
static void write(std::ostream& os, const T val) {
    os.write((const char*) &val, sizeof val);
}


template <typename T>
static T read(std::istream& is) {
    T val;
    is.read((char *) &val, sizeof val);
    return val;
}


static void write_str(std::ostream& os, const std::string& val) {
    auto size = val.size();
    write(os, size);
    os.write(val.c_str(), size);
}


static std::string read_str(std::istream& is) {
    size_t size = read<size_t>(is);
    char* data = new char[size];
    is.read(data, size);
    std::string retval(data, size);
    delete[] data;
    return retval;
}


Serializer& Serializer::operator<<(const std::string& str) {
    write_str(os, str);
    return *this;
}


Serializer& Serializer::operator<<(const Object& obj) {
    obj.serialize(*this);
    return *this;
}


Serializer& Serializer::operator<<(const AstNode& node) {
    node.serialize(*this);
    return *this;
}


void Object::serialize(std::ostream& os) const {
    Serializer(os) << *this;
}


void Object::serialize(Serializer& os) const {
    switch (type()) {
    case Type::integer:
        os << 'I' << unsafe_integer();
        break;
    case Type::string:
        os << 'S' << unsafe_string();
        break;
    case Type::boolean:
        os << 'B' << unsafe_boolean();
        break;
    case Type::floating:
        os << 'F' << unsafe_floating();
        break;
    case Type::null:
        os << 'N';
        break;
    case Type::map:
        os << 'M' << unsafe_map()->size();
        for (auto& [key, value] : *unsafe_map())
            os << key << value;
        break;
    case Type::list:
        os << 'L' << unsafe_list()->size();
        for (auto& value : *unsafe_list())
            os << value;
        break;
    case Type::closure: {
        auto closure = std::get<Closure>(_data);
        os << 'C' << closure->nonlocals.size();
        for (auto& [key, value] : closure->nonlocals)
            os << key << value;
        os << closure->parameters.size();
        for (auto& p : closure->parameters)
            os << p;
        os << *closure->expression;
        break;
    }
    case Type::builtin:
        os << 'U' << std::get<Builtin>(_data).name;
        break;
    }
}


Object Object::deserialize(std::string val) {
    std::istringstream is(val);
    return deserialize(is);
}


Object Object::deserialize(std::istream& is) {
    char indicator;
    is >> indicator;
    switch (indicator) {
    case 'I':
        return Object::integer(read<Integer>(is));
    case 'S':
        return Object::string(read_str(is));
    case 'B':
        return Object::boolean(read<bool>(is));
    case 'F':
        return Object::floating(read<double>(is));
    case 'N':
        return Object::null();
    case 'M': {
        auto size = read<size_t>(is);
        Object::MapT map;
        for (size_t i = 0; i < size; i++) {
            auto key = read_str(is);
            auto val = Object::deserialize(is);
            map[key] = val;
        }
        return Object::map(std::move(map));
    }
    case 'L': {
        auto size = read<size_t>(is);
        Object::ListT list;
        for (size_t i = 0; i < size; i++)
            list.push_back(Object::deserialize(is));
        return Object::list(std::move(list));
    }
    case 'C': {
        auto closure = std::make_shared<ClosureT>();
        auto size = read<size_t>(is);
        for (size_t i = 0; i < size; i++) {
            auto key = read_str(is);
            auto value = Object::deserialize(is);
            closure->nonlocals[key] = value;
        }
        size = read<size_t>(is);
        for (size_t i = 0; i < size; i++)
            closure->parameters.push_back(read_str(is));
        closure->expression = AstNode::deserialize(is);
        return Object::closure(closure);
    }
    case 'U':
        return builtins[read_str(is)];
    }

    throw InternalException();
}


void Source::serialize(std::ostream& os) const {
    write(os, byte);
    write(os, line);
    write(os, column);
}


Source Source::deserialize(std::istream& is) {
    auto byte = read<size_t>(is);
    auto line = read<size_t>(is);
    auto column = read<size_t>(is);
    return Source { byte, line, column };
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
    os << 'F' << source() << parameters.size();
    for (auto& p : parameters)
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


std::unique_ptr<AstNode> AstNode::deserialize(std::string val) {
    std::istringstream is(val);
    return deserialize(is);
}


std::unique_ptr<AstNode> AstNode::deserialize(std::istream& is) {
    char indicator;
    is >> indicator;
    auto source = Source::deserialize(is);
    switch (indicator) {
    case 'T':
        return std::make_unique<Literal>(source, Object::deserialize(is));
    case 'I':
        return std::make_unique<Identifier>(source, read_str(is));
    case 'L': {
        auto list = std::make_unique<List>(source);
        auto size = read<size_t>(is);
        for (size_t i = 0; i < size; i++) {
            auto node = AstNode::deserialize(is);
            auto splat = read<bool>(is);
            list->append(std::move(node), splat);
        }
        return list;
    }
    case 'M': {
        auto map = std::make_unique<Map>(source);
        auto size = read<size_t>(is);
        for (size_t i = 0; i < size; i++) {
            auto key = read_str(is);
            auto value = AstNode::deserialize(is);
            auto splat = read<bool>(is);
            map->append(key, std::move(value), splat);
        }
        return map;
    }
    case 'O': {
        auto lhs = AstNode::deserialize(is);
        auto op = read<Operator>(is);
        auto rhs = AstNode::deserialize(is);
        return std::make_unique<BinOp>(source, std::move(lhs), std::move(rhs), op);
    }
    case 'B': {
        auto block = std::make_unique<Block>(source);
        auto size = read<size_t>(is);
        for (size_t i = 0; i < size; i++) {
            auto key = read_str(is);
            auto value = AstNode::deserialize(is);
            block->append(key, std::move(value));
        }
        block->set_expression(AstNode::deserialize(is));
        return block;
    }
    case 'F': {
        auto func = std::make_unique<Function>(source);
        auto size = read<size_t>(is);
        for (size_t i = 0; i < size; i++)
            func->append(read_str(is));
        func->set_expression(AstNode::deserialize(is));
        return func;
    }
    case 'C': {
        auto cond = AstNode::deserialize(is);
        auto yes = AstNode::deserialize(is);
        auto no = AstNode::deserialize(is);
        return std::make_unique<Branch>(source, std::move(cond), std::move(yes), std::move(no));
    }
    case 'E': {
        auto call = std::make_unique<FunCall>(source, AstNode::deserialize(is));
        auto size = read<size_t>(is);
        for (size_t i = 0; i < size; i++)
            call->append(AstNode::deserialize(is));
        return call;
    }
    case 'S': {
        auto container = AstNode::deserialize(is);
        auto index = AstNode::deserialize(is);
        return std::make_unique<Index>(source, std::move(container), std::move(index));
    }
    default:
        throw InternalException();
    }
}
