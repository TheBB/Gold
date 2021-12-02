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
    enum class Type { literal, list, map };

    using Literal = Object;
    using List = std::vector<AstNode>;
    using Map = std::vector<std::pair<std::string, AstNode>>;

private:
    std::variant<Literal, List, Map> _data;

public:
    // Raw constructors
    AstNode(Object value) : _data(value) {}
    AstNode(List value) : _data(value) {}
    AstNode(Map value) : _data(value) {}

    // Type inspection
    Type type() const {
        if (std::holds_alternative<Literal>(_data)) return Type::literal;
        if (std::holds_alternative<List>(_data)) return Type::list;
        return Type::map;
    }

    // Unsafe getters
    Object unsafe_object() const { return std::get<Literal>(_data); }
    const List& unsafe_list() const { return std::get<List>(_data); }
    const Map& unsafe_map() const { return std::get<Map>(_data); }

    void dump(std::ostream&) const;
};

bool analyze_grammar();
AstNode parse(std::string);
void debug_parse(std::string);
void debug_parse_tree(std::string);

}

std::ostream& operator<<(std::ostream&, const Gold::AstNode&);
