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
    using Literal = Object;
    using List = std::vector<std::unique_ptr<AstNode>>;

private:
    std::variant<Literal, List> _data;

public:
    AstNode(Object value) : _data(value) {}
    // AstNode(List value) : _data(value) {}

    Object object() const { return std::get<Literal>(_data); }

    void dump(std::ostream&) const;
};

bool analyze_grammar();
std::unique_ptr<AstNode> parse(std::string);
void debug_parse(std::string);

}

std::ostream& operator<<(std::ostream&, const Gold::AstNode&);
