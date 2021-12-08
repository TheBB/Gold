#include "gold.hpp"

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
    case Type::undefined:
        os << 'U';
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
    case 'U':
        return Object::undefined();
    }
}
