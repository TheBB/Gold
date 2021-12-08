#include <set>
#include <string>

#include "gold.hpp"

#pragma once


namespace Gold
{

struct ParseException: public std::exception {};


enum class Operator {
    plus,
    minus,
    multiply,
    divide,
    integer_divide
};


class Literal : public AstNode {
private:
    const Object object;
public:
    Literal(Object obj) : object(obj) {}
    virtual void dump(std::ostream& os) const { os << "Lit(" << object << ")"; }
    virtual void free_identifiers(std::set<std::string>&) const {}
    virtual Object evaluate(EvaluationContext&) const { return object; }
};


class Identifier : public AstNode {
private:
    const std::string name;
public:
    Identifier(std::string name) : name(name) {}
    Identifier(std::string& name) : name(name) {}
    virtual void dump(std::ostream& os) const { os << "Id(" << name << ")"; }
    virtual void free_identifiers(std::set<std::string>& idents) const { idents.insert(name); }
    virtual Object evaluate(EvaluationContext& ctx) const { return ctx.lookup(name); }
};


class List : public AstNode {
private:
    std::vector<std::unique_ptr<AstNode>> elements;
public:
    void append(std::unique_ptr<AstNode> node) { elements.push_back(std::move(node)); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
};


class Map : public AstNode {
private:
    std::vector<std::pair<std::string, std::unique_ptr<AstNode>>> entries;
public:
    void append(std::string key, std::unique_ptr<AstNode> value) {
        entries.push_back(std::pair(key, std::move(value)));
    }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
};


class OpSeq : public AstNode {
private:
    std::unique_ptr<AstNode> initial;
    std::vector<std::pair<Operator, std::unique_ptr<AstNode>>> sequence;
public:
    OpSeq(std::unique_ptr<AstNode> init) : initial(std::move(init)) {}
    void append(Operator op, std::unique_ptr<AstNode> operand) {
        sequence.push_back(std::pair(op, std::move(operand)));
    }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
};


class Block : public AstNode {
private:
    std::vector<std::pair<std::string, std::unique_ptr<AstNode>>> bindings;
    std::unique_ptr<AstNode> expression;
public:
    void append(std::string key, std::unique_ptr<AstNode> value) {
        bindings.push_back(std::pair(key, std::move(value)));
    }
    void set_expression(std::unique_ptr<AstNode> expr) { expression = std::move(expr); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
};


class Function : public AstNode {
private:
    std::vector<std::string> parameters;
    std::unique_ptr<AstNode> expression;
public:
    void append(std::string key) { parameters.push_back(key); }
    void set_expression(std::unique_ptr<AstNode> expr) { expression = std::move(expr); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
};


class Branch : public AstNode {
private:
    std::unique_ptr<AstNode> condition;
    std::unique_ptr<AstNode> if_value;
    std::unique_ptr<AstNode> else_value;
public:
    Branch(std::unique_ptr<AstNode> cond, std::unique_ptr<AstNode> yes, std::unique_ptr<AstNode> no)
        : condition(std::move(cond)), if_value(std::move(yes)), else_value(std::move(no)) { }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
};


class FunCall : public AstNode {
private:
    std::unique_ptr<AstNode> function;
    std::vector<std::unique_ptr<AstNode>> args;
public:
    FunCall(std::unique_ptr<AstNode> func) : function(std::move(func)) {}
    void append(std::unique_ptr<AstNode> arg) { args.push_back(std::move(arg)); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
};


class Index : public AstNode {
private:
    std::unique_ptr<AstNode> haystack;
    std::unique_ptr<AstNode> needle;
public:
    Index(std::unique_ptr<AstNode> object, std::unique_ptr<AstNode> index)
        : haystack(std::move(object)), needle(std::move(index)) {}
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
};


bool analyze_grammar();
std::unique_ptr<AstNode> parse(std::string, bool as_expression = true);
void debug_parse(std::string, bool as_expression = true);
void debug_parse_tree(std::string, bool as_expression = true);

}

std::ostream& operator<<(std::ostream&, const Gold::AstNode&);
std::ostream& operator<<(std::ostream&, Gold::Operator);
std::ostream& operator<<(std::ostream&, Gold::Operator);
