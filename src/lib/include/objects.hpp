#include <cinttypes>

#include "gold.hpp"

#pragma once


namespace Gold {


class GObject {
public:
    virtual Type type() const = 0;
};


class Integer: public GObject {
private:
    intmax_t _value;

public:
    Integer(intmax_t value) : _value(value) {}

    Type type() const { return Type::integer; }
    intmax_t value() const { return _value; }
};


class String: public GObject {
private:
    std::string _string;

public:
    String(const std::string& string) : _string(string) {}

    Type type() const { return Type::string; }
    const std::string& string() const { return _string; }
};


class Boolean: public GObject {
private:
    bool _value;

public:
    Boolean(bool value) : _value(value) {}

    Type type() const { return Type::boolean; }
    bool value() const { return _value; }
};


class Floating: public GObject {
private:
    double _value;

public:
    Floating(double value) : _value(value) {}

    Type type() const { return Type::floating; }
    double value() const { return _value; }
};


class Map: public GObject {
private:
    std::map<std::string, Object> _elements;

public:
    Map(std::map<std::string, Object> elements) : _elements(elements) {}

    Type type() const { return Type::map; }
    const std::map<std::string, Object>& map() const { return _elements; }
};


class List: public GObject {
private:
    std::vector<Object> _elements;

public:
    List(std::vector<Object> elements) : _elements(elements) {}

    Type type() const { return Type::list; }
    const std::vector<Object>& list() const { return _elements; }
};


class Error: public GObject {
private:
    std::string _message;

public:
    Error(const std::string& message) : _message(message) {}

    Type type() const { return Type::error; }
    const std::string& message() const { return _message; }
};


}
