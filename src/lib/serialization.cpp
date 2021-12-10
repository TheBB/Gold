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


void Object::serialize(std::ostream& os) const {
    switch (type()) {
    case Type::integer:
        os << 'I';
        write(os, unsafe_integer());
        break;
    case Type::string:
        os << 'S';
        write_str(os, unsafe_string());
        break;
    case Type::boolean:
        os << 'B' << (unsafe_boolean() ? '1' : '0');
        break;
    case Type::floating:
        os << 'F';
        write(os, unsafe_floating());
        break;
    case Type::null:
        os << 'N';
        break;
    case Type::map:
        os << 'M';
        write(os, unsafe_map()->size());
        for (auto& [key, value] : *unsafe_map()) {
            write_str(os, key);
            value.serialize(os);
        }
        break;
    case Type::list:
        os << 'L';
        write(os, unsafe_list()->size());
        for (auto& value : *unsafe_list())
            value.serialize(os);
        break;
    case Type::closure:
        os << 'C';
        write(os, unsafe_closure()->nonlocals.size());
        for (auto& [key, value] : unsafe_closure()->nonlocals) {
            write_str(os, key);
            value.serialize(os);
        }
        write(os, unsafe_closure()->parameters.size());
        for (auto& p : unsafe_closure()->parameters)
            write_str(os, p);
        unsafe_closure()->expression->serialize(os);
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
    case 'B': {
        char val;
        is >> val;
        return Object::boolean(val == '1' ? true : false);
    }
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
    }

    throw std::exception();
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


void Literal::serialize(std::ostream& os) const {
    os << 'T';
    source().serialize(os);
    object.serialize(os);
}


void Identifier::serialize(std::ostream& os) const {
    os << 'I';
    source().serialize(os);
    write_str(os, name);
}


void List::serialize(std::ostream& os) const {
    os << 'L';
    source().serialize(os);
    write(os, elements.size());
    for (auto& value : elements)
        value->serialize(os);
}


void Map::serialize(std::ostream& os) const {
    os << 'M';
    source().serialize(os);
    write(os, entries.size());
    for (auto& [key, value] : entries) {
        write_str(os, key);
        value->serialize(os);
    }
}


void BinOp::serialize(std::ostream& os) const {
    os << 'O';
    source().serialize(os);
    lhs->serialize(os);
    write(os, op);
    rhs->serialize(os);
}


void Block::serialize(std::ostream& os) const {
    os << 'B';
    source().serialize(os);
    write(os, bindings.size());
    for (auto& [key, value] : bindings) {
        write_str(os, key);
        value->serialize(os);
    }
    expression->serialize(os);
}


void Function::serialize(std::ostream& os) const {
    os << 'F';
    source().serialize(os);
    write(os, parameters.size());
    for (auto& p : parameters)
        write_str(os, p);
    expression->serialize(os);
}


void Branch::serialize(std::ostream& os) const {
    os << 'C';
    source().serialize(os);
    condition->serialize(os);
    if_value->serialize(os);
    else_value->serialize(os);
}


void FunCall::serialize(std::ostream& os) const {
    os << 'E';
    source().serialize(os);
    function->serialize(os);
    write(os, args.size());
    for (auto& arg : args)
        arg->serialize(os);
}


void Index::serialize(std::ostream& os) const {
    os << 'S';
    source().serialize(os);
    haystack->serialize(os);
    needle->serialize(os);
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
        for (size_t i = 0; i < size; i++)
            list->append(AstNode::deserialize(is));
        return list;
    }
    case 'M': {
        auto map = std::make_unique<Map>(source);
        auto size = read<size_t>(is);
        for (size_t i = 0; i < size; i++) {
            auto key = read_str(is);
            auto value = AstNode::deserialize(is);
            map->append(key, std::move(value));
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
        throw std::exception();
    }
}
