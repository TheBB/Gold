#include <set>
#include <string>

#include <tao/pegtl/contrib/parse_tree.hpp>

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
    integer_divide,
    less_than,
    less_than_or_eq,
    greater_than,
    greater_than_or_eq,
    equal,
    not_equal,
    conjunction,
    disjunction
};


struct Literal : public AstNode {
    const Object object;

    Literal(Source source, Object obj) : AstNode(source), object(obj) {}
    virtual void dump(std::ostream& os) const { os << "Lit(" << object << ")"; }
    virtual void free_identifiers(std::set<std::string>&) const {}
    virtual Object evaluate(EvaluationContext&) const { return object; }
    virtual void serialize(Serializer&) const;
};


struct Identifier : public AstNode {
    const std::string name;

    Identifier(Source source, std::string name) : AstNode(source), name(name) {}
    Identifier(Source source, std::string& name) : AstNode(source), name(name) {}
    virtual void dump(std::ostream& os) const { os << "Id(" << name << ")"; }
    virtual void free_identifiers(std::set<std::string>& idents) const { idents.insert(name); }
    virtual Object evaluate(EvaluationContext& ctx) const;
    virtual void serialize(Serializer&) const;
};


struct List : public AstNode {
    using Entry = struct {
        AstPtr node;
        bool splat;
    };

    std::vector<Entry> elements;

    List(Source source) : AstNode(source) {}
    List(Source source, std::vector<Entry> entries) : AstNode(source), elements(std::move(entries)) {}
    void append(AstPtr node, bool splat) { elements.push_back({std::move(node), splat}); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(Serializer&) const;
};


struct Map : public AstNode {
    using Entry = struct {
        std::string key;
        AstPtr node;
        bool splat;
    };

    std::vector<Entry> entries;

    Map(Source source) : AstNode(source) {}
    Map(Source source, std::vector<Entry> elements) : AstNode(source), entries(std::move(elements)) {}
    void append(std::string key, AstPtr value, bool splat) {
        entries.push_back({key, std::move(value), splat});
    }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(Serializer&) const;
};


struct BinOp : public AstNode {
    AstPtr lhs, rhs;
    Operator op;

    BinOp(Source source, AstPtr l, AstPtr r, Operator oper)
        : AstNode(source), lhs(std::move(l)), rhs(std::move(r)), op(oper) {}
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(Serializer&) const;
};


struct Block : public AstNode {
    std::vector<std::pair<std::string, AstPtr>> bindings;
    AstPtr expression;

    Block(Source source) : AstNode(source) {}
    Block(Source source, std::vector<std::pair<std::string, AstPtr>> entries, AstPtr expr) :
        AstNode(source), bindings(std::move(entries)), expression(std::move(expr)) {}
    void append(std::string key, AstPtr value) {
        bindings.push_back(std::pair(key, std::move(value)));
    }
    void set_expression(AstPtr expr) { expression = std::move(expr); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(Serializer&) const;
};


struct Function : public AstNode {
    std::shared_ptr<std::vector<std::string>> parameters;
    std::shared_ptr<AstNode> expression;

    Function(Source source) : AstNode(source), parameters(new std::vector<std::string>()) {}
    Function(Source source, std::shared_ptr<std::vector<std::string>> p, std::shared_ptr<AstNode> x)
        : AstNode(source), parameters(p), expression(std::move(x)) {}
    void append(std::string key) { parameters->push_back(key); }
    void set_expression(AstPtr expr) { expression = std::move(expr); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(Serializer&) const;
};


struct Branch : public AstNode {
    AstPtr condition;
    AstPtr if_value;
    AstPtr else_value;

    Branch(
        Source source, AstPtr cond,
        AstPtr yes, AstPtr no
    ) : AstNode(source), condition(std::move(cond)), if_value(std::move(yes)), else_value(std::move(no)) { }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(Serializer&) const;
};


struct FunCall : public AstNode {
    AstPtr function;
    std::vector<AstPtr> args;

    FunCall(Source source, AstPtr func) : AstNode(source), function(std::move(func)) {}
    FunCall(Source source, AstPtr func, std::vector<AstPtr> a) : AstNode(source), function(std::move(func)), args(std::move(a)) {}
    void append(AstPtr arg) { args.push_back(std::move(arg)); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(Serializer&) const;
};


struct Index : public AstNode {
    AstPtr haystack;
    AstPtr needle;

    Index(Source source, AstPtr object, AstPtr index)
        : AstNode(source), haystack(std::move(object)), needle(std::move(index)) {}
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void serialize(Serializer&) const;
};


bool analyze_grammar();
AstPtr parse_string(std::string);
AstPtr parse_file(std::string);
void debug_parse(std::string);
void debug_parse_tree(std::string);

AstPtr normalize(tao::pegtl::parse_tree::node&);

}

std::ostream& operator<<(std::ostream&, const Gold::AstNode&);
std::ostream& operator<<(std::ostream&, Gold::Operator);
std::ostream& operator<<(std::ostream&, Gold::Operator);
