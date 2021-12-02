#include <optional>
#include <string>
#include <variant>

#include "gold.hpp"

#pragma once


namespace Gold
{

struct ParseException: public std::exception {};

class AstNode {
public:
    enum class Type { literal, list };

    using Literal = Object;
    using List = std::vector<AstNode>;

private:
    std::variant<Literal, List> _data;

public:
    // Raw constructors
    AstNode(Object value) : _data(value) {}
    AstNode(List value) : _data(value) {}

    // Type inspection
    Type type() const {
        if (std::holds_alternative<Literal>(_data)) return Type::literal;
        return Type::list;
    }

    // Unsafe getters
    Object unsafe_object() const { return std::get<Literal>(_data); }
    const List& unsafe_list() const { return std::get<List>(_data); }

    void dump(std::ostream&) const;
};

bool analyze_grammar();
AstNode parse(std::string);
void debug_parse(std::string);

}

std::ostream& operator<<(std::ostream&, const Gold::AstNode&);
