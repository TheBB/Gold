#include <map>
#include <memory>
#include <vector>

#pragma once


namespace Gold {


enum Type { integer, string, boolean, floating, map, list, function, error };

class GObject;


class Object {
private:
    const std::shared_ptr<GObject> _object;

public:
    Object(std::shared_ptr<GObject> object) : _object(object) {}
    static Object integer(int);
    static Object string(const std::string&);
    static Object boolean(bool);
    static Object floating(double);
    static Object map(std::map<std::string, Object>);
    static Object list(std::vector<Object>);
    static Object error(const std::string&);

    Type type() const;
    std::string type_name() const;
    bool is_error() const { return type() == Type::error; }

    // Unsafe getters
    int unsafe_integer() const;
    const std::string& unsafe_string() const;
    bool unsafe_boolean() const;
    double unsafe_floating() const;
    const std::map<std::string, Object>& unsafe_map() const;
    const std::vector<Object>& unsafe_list() const;
    const std::string& unsafe_error() const;

    Object operator+(Object other);
    Object operator-(Object other);
};


}


std::ostream& operator<<(std::ostream& os, const Gold::Object& obj);
