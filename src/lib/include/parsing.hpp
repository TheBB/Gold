#include <optional>
#include <string>
#include <variant>

#include "gold.hpp"

#pragma once


namespace Gold
{

class AstNode;

struct ParseException: public std::exception {};

enum class Operator {
    plus,
    minus,
    multiply,
    divide,
    integer_divide
};

class AstNode {
public:
    enum class Type { literal, identifier, list, map, opseq, block, function, conditional };

    using Literal = Object;
    using Identifier = std::string;
    using List = std::vector<AstNode>;
    using Map = std::vector<std::pair<std::string, AstNode>>;
    using Operator = struct {
        std::vector<AstNode> operands;
        std::vector<Operator> operators;
    };
    using Block = struct {
        std::vector<std::pair<std::string, AstNode>> bindings;
        std::unique_ptr<AstNode> expression;
    };
    using Function = struct {
        std::vector<std::string> params;
        std::unique_ptr<AstNode> expression;
    };
    using Conditional = struct {
        std::unique_ptr<AstNode> condition;
        std::unique_ptr<AstNode> if_branch;
        std::unique_ptr<AstNode> else_branch;
    };

private:
    std::variant<Literal, Identifier, List, Map, Operator, Block, Function, Conditional> _data;

public:
    // Raw constructors
    AstNode(Object value) : _data(value) {}
    AstNode(Identifier value) : _data(value) {}
    AstNode(List&& value) : _data(std::move(value)) {}
    AstNode(Map&& value) : _data(std::move(value)) {}
    AstNode(Operator&& value) : _data(std::move(value)) {}
    AstNode(Block&& value) : _data(std::move(value)) {}
    AstNode(Function&& value) : _data(std::move(value)) {}
    AstNode(Conditional&& value) : _data(std::move(value)) {}

    // Type inspection
    Type type() const {
        if (std::holds_alternative<Literal>(_data)) return Type::literal;
        if (std::holds_alternative<Identifier>(_data)) return Type::identifier;
        if (std::holds_alternative<List>(_data)) return Type::list;
        if (std::holds_alternative<Map>(_data)) return Type::map;
        if (std::holds_alternative<Operator>(_data)) return Type::opseq;
        if (std::holds_alternative<Block>(_data)) return Type::block;
        if (std::holds_alternative<Function>(_data)) return Type::function;
        return Type::conditional;
    }

    // Unsafe getters
    Object unsafe_object() const { return std::get<Literal>(_data); }
    const Identifier& unsafe_identifier() const { return std::get<Identifier>(_data); }
    const List& unsafe_list() const { return std::get<List>(_data); }
    const Map& unsafe_map() const { return std::get<Map>(_data); }
    const Operator& unsafe_opseq() const { return std::get<Operator>(_data); }
    const Block& unsafe_block() const { return std::get<Block>(_data); }
    const Function& unsafe_function() const { return std::get<Function>(_data); }
    const Conditional& unsafe_conditional() const { return std::get<Conditional>(_data); }

    void dump(std::ostream&) const;
};

bool analyze_grammar();
AstNode parse(std::string);
void debug_parse(std::string);
void debug_parse_tree(std::string);

}

std::ostream& operator<<(std::ostream&, const Gold::AstNode&);
std::ostream& operator<<(std::ostream&, Gold::Operator);
