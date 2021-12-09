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
    Literal(Source source, Object obj) : AstNode(source), object(obj) {}
    virtual void dump(std::ostream& os) const { os << "Lit(" << object << ")"; }
    virtual void free_identifiers(std::set<std::string>&) const {}
    virtual Object evaluate(EvaluationContext&) const { return object; }
    virtual void serialize(std::ostream&) const;
};


class Identifier : public AstNode {
private:
    const std::string name;
public:
    Identifier(Source source, std::string name) : AstNode(source), name(name) {}
    Identifier(Source source, std::string& name) : AstNode(source), name(name) {}
    virtual void dump(std::ostream& os) const { os << "Id(" << name << ")"; }
    virtual void free_identifiers(std::set<std::string>& idents) const { idents.insert(name); }
    virtual Object evaluate(EvaluationContext& ctx) const;
    virtual void serialize(std::ostream&) const;
};


class List : public AstNode {
private:
    std::vector<std::unique_ptr<AstNode>> elements;
public:
    List(Source source) : AstNode(source) {}
    void append(std::unique_ptr<AstNode> node) { elements.push_back(std::move(node)); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(std::ostream&) const;
};


class Map : public AstNode {
private:
    std::vector<std::pair<std::string, std::unique_ptr<AstNode>>> entries;
public:
    Map(Source source) : AstNode(source) {}
    void append(std::string key, std::unique_ptr<AstNode> value) {
        entries.push_back(std::pair(key, std::move(value)));
    }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(std::ostream&) const;
};


class OpSeq : public AstNode {
private:
    std::unique_ptr<AstNode> initial;
    std::vector<std::pair<Operator, std::unique_ptr<AstNode>>> sequence;
public:
    OpSeq(Source source, std::unique_ptr<AstNode> init) : AstNode(source), initial(std::move(init)) {}
    void append(Operator op, std::unique_ptr<AstNode> operand) {
        sequence.push_back(std::pair(op, std::move(operand)));
    }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(std::ostream&) const;
};


class Block : public AstNode {
private:
    std::vector<std::pair<std::string, std::unique_ptr<AstNode>>> bindings;
    std::unique_ptr<AstNode> expression;
public:
    Block(Source source) : AstNode(source) {}
    void append(std::string key, std::unique_ptr<AstNode> value) {
        bindings.push_back(std::pair(key, std::move(value)));
    }
    void set_expression(std::unique_ptr<AstNode> expr) { expression = std::move(expr); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(std::ostream&) const;
};


class Function : public AstNode {
private:
    std::vector<std::string> parameters;
    std::unique_ptr<AstNode> expression;
public:
    Function(Source source) : AstNode(source) {}
    void append(std::string key) { parameters.push_back(key); }
    void set_expression(std::unique_ptr<AstNode> expr) { expression = std::move(expr); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(std::ostream&) const;
};


class Branch : public AstNode {
private:
    std::unique_ptr<AstNode> condition;
    std::unique_ptr<AstNode> if_value;
    std::unique_ptr<AstNode> else_value;
public:
    Branch(
        Source source, std::unique_ptr<AstNode> cond,
        std::unique_ptr<AstNode> yes, std::unique_ptr<AstNode> no
    ) : AstNode(source), condition(std::move(cond)), if_value(std::move(yes)), else_value(std::move(no)) { }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(std::ostream&) const;
};


class FunCall : public AstNode {
private:
    std::unique_ptr<AstNode> function;
    std::vector<std::unique_ptr<AstNode>> args;
public:
    FunCall(Source source, std::unique_ptr<AstNode> func) : AstNode(source), function(std::move(func)) {}
    void append(std::unique_ptr<AstNode> arg) { args.push_back(std::move(arg)); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(std::ostream&) const;
};


class Index : public AstNode {
private:
    std::unique_ptr<AstNode> haystack;
    std::unique_ptr<AstNode> needle;
public:
    Index(Source source, std::unique_ptr<AstNode> object, std::unique_ptr<AstNode> index)
        : AstNode(source), haystack(std::move(object)), needle(std::move(index)) {}
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(std::ostream&) const;
};


bool analyze_grammar();
std::unique_ptr<AstNode> parse(std::string, bool as_expression = true);
void debug_parse(std::string, bool as_expression = true);
void debug_parse_tree(std::string, bool as_expression = true);

}

std::ostream& operator<<(std::ostream&, const Gold::AstNode&);
std::ostream& operator<<(std::ostream&, Gold::Operator);
std::ostream& operator<<(std::ostream&, Gold::Operator);
