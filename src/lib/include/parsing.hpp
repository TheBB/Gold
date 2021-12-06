#include <optional>
#include <string>
#include <variant>

#include "gold.hpp"

#pragma once


namespace Gold::Ast
{

struct ParseException: public std::exception {};

enum class Operator {
    plus,
    minus,
    multiply,
    divide,
    integer_divide
};


class Node {
public:
    virtual void dump(std::ostream&) const = 0;
    std::string dump() const;
};


class Literal : public Node {
private:
    const Object object;
public:
    Literal(Object obj) : object(obj) {}
    virtual void dump(std::ostream& os) const { os << "Lit(" << object << ")"; }
};


class Identifier : public Node {
private:
    const std::string name;
public:
    Identifier(std::string name) : name(name) {}
    Identifier(std::string& name) : name(name) {}
    virtual void dump(std::ostream& os) const { os << "Id(" << name << ")"; }
};


class List : public Node {
private:
    std::vector<std::unique_ptr<Node>> elements;
public:
    void append(std::unique_ptr<Node> node) { elements.push_back(std::move(node)); }
    virtual void dump(std::ostream&) const;
};


class Map : public Node {
private:
    std::vector<std::pair<std::string, std::unique_ptr<Node>>> entries;
public:
    void append(std::string key, std::unique_ptr<Node> value) {
        entries.push_back(std::pair(key, std::move(value)));
    }
    virtual void dump(std::ostream&) const;
};


class OpSeq : public Node {
private:
    std::unique_ptr<Node> initial;
    std::vector<std::pair<Operator, std::unique_ptr<Node>>> sequence;
public:
    OpSeq(std::unique_ptr<Node> init) : initial(std::move(init)) {}
    void append(Operator op, std::unique_ptr<Node> operand) {
        sequence.push_back(std::pair(op, std::move(operand)));
    }
    virtual void dump(std::ostream&) const;
};


class Block : public Node {
private:
    std::vector<std::pair<std::string, std::unique_ptr<Node>>> bindings;
    std::unique_ptr<Node> expression;
public:
    void append(std::string key, std::unique_ptr<Node> value) {
        bindings.push_back(std::pair(key, std::move(value)));
    }
    void set_expression(std::unique_ptr<Node> expr) { expression = std::move(expr); }
    virtual void dump(std::ostream&) const;
};


class Function : public Node {
private:
    std::vector<std::string> parameters;
    std::unique_ptr<Node> expression;
public:
    void append(std::string key) { parameters.push_back(key); }
    void set_expression(std::unique_ptr<Node> expr) { expression = std::move(expr); }
    virtual void dump(std::ostream&) const;
};


class Branch : public Node {
private:
    std::unique_ptr<Node> condition;
    std::unique_ptr<Node> if_value;
    std::unique_ptr<Node> else_value;
public:
    Branch(std::unique_ptr<Node> cond, std::unique_ptr<Node> yes, std::unique_ptr<Node> no)
        : condition(std::move(cond)), if_value(std::move(yes)), else_value(std::move(no)) { }
    virtual void dump(std::ostream&) const;
};


class FunCall : public Node {
private:
    std::unique_ptr<Node> function;
    std::vector<std::unique_ptr<Node>> args;
public:
    FunCall(std::unique_ptr<Node> func) : function(std::move(func)) {}
    void append(std::unique_ptr<Node> arg) { args.push_back(std::move(arg)); }
    virtual void dump(std::ostream&) const;
};


class Index : public Node {
private:
    std::unique_ptr<Node> haystack;
    std::unique_ptr<Node> needle;
public:
    Index(std::unique_ptr<Node> object, std::unique_ptr<Node> index)
        : haystack(std::move(object)), needle(std::move(index)) {}
    virtual void dump(std::ostream&) const;
};


bool analyze_grammar();
std::unique_ptr<Node> parse(std::string, bool as_expression = true);
void debug_parse(std::string, bool as_expression = true);
void debug_parse_tree(std::string, bool as_expression = true);

}

std::ostream& operator<<(std::ostream&, const Gold::Ast::Node&);
std::ostream& operator<<(std::ostream&, Gold::Ast::Operator);
std::ostream& operator<<(std::ostream&, Gold::Ast::Operator);
