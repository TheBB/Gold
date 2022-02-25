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


struct AstNode : public Serializable {
    Source src;

    AstNode(Source src) : src(src) {}
    virtual ~AstNode() {};
    virtual void dump(std::ostream&) const = 0;
    std::string dump() const;
    virtual void free_identifiers(std::set<std::string>&) const = 0;
    std::set<std::string> free_identifiers() const;
    virtual Object evaluate(EvaluationContext&) const = 0;

    static std::unique_ptr<AstNode> deserialize(std::string);
    static std::unique_ptr<AstNode> deserialize(std::istream&);
    static std::unique_ptr<AstNode> deserialize(Deserializer&);
    // static AstNode* deserialize_raw(Deserializer&);

    const Source source() const { return src; }
};


struct Literal : public AstNode {
    const Object object;

    Literal(Source src, Object object) : AstNode(src), object(object) {}
    virtual void dump(std::ostream& os) const { os << "Lit(" << object << ")"; }
    virtual void free_identifiers(std::set<std::string>&) const {}
    virtual Object evaluate(EvaluationContext&) const { return object; }
    virtual void do_serialize(Serializer&) const;
};


struct Identifier : public AstNode {
    const std::string name;

    Identifier(Source src, std::string name) : AstNode(src), name(name) {}
    virtual void dump(std::ostream& os) const { os << "Id(" << name << ")"; }
    virtual void free_identifiers(std::set<std::string>& idents) const { idents.insert(name); }
    virtual Object evaluate(EvaluationContext& ctx) const;
    virtual void do_serialize(Serializer&) const;
};


struct List : public AstNode {
    using Entry = struct {
        AstPtr node;
        bool splat;
    };

    std::vector<Entry> elements;

    List(Source src) : AstNode(src) {}
    List(Source src, std::vector<Entry> elements)
        : AstNode(src), elements(std::move(elements)) {}
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct Map : public AstNode {
    using Entry = struct {
        std::string key;
        AstPtr node;
        bool splat;
    };

    std::vector<Entry> entries;

    Map(Source src) : AstNode(src) {}
    Map(Source src, std::vector<Entry> entries)
        : AstNode(src), entries(std::move(entries)) {}
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct BinOp : public AstNode {
    AstPtr lhs, rhs;
    Operator op;

    BinOp(Source src, AstPtr l, AstPtr r, Operator oper)
        : AstNode(src), lhs(std::move(l)), rhs(std::move(r)), op(oper) {}
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct Block : public AstNode {
    using Binding = struct {
        std::string name;
        AstPtr expression;
    };

    std::vector<Binding> bindings;
    AstPtr expression;

    Block(Source src) : AstNode(src) {}
    Block(Source src, std::vector<Binding> bindings, AstPtr expression)
        : AstNode(src), bindings(std::move(bindings)), expression(std::move(expression)) {}
    void set_expression(AstPtr expr) { expression = std::move(expr); }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct Function : public AstNode {
    std::shared_ptr<std::vector<std::string>> parameters;
    std::shared_ptr<AstNode> expression;

    Function(Source src)
        : AstNode(src), parameters(new std::vector<std::string>()), expression(nullptr) {}
    Function(Source src, std::shared_ptr<std::vector<std::string>> parameters, std::shared_ptr<AstNode> expression)
        : AstNode(src), parameters(parameters), expression(expression) {}
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct Branch : public AstNode {
    AstPtr condition;
    AstPtr if_value;
    AstPtr else_value;

    Branch(Source src, AstPtr cond, AstPtr yes, AstPtr no)
        : AstNode(src), condition(std::move(cond)), if_value(std::move(yes)), else_value(std::move(no)) { }
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct FunCall : public AstNode {
    AstPtr function;
    std::vector<AstPtr> args;

    FunCall(Source src, AstPtr function) : AstNode(src), function(std::move(function)) {}
    FunCall(Source src, AstPtr function, std::vector<AstPtr> args)
        : AstNode(src), function(std::move(function)), args(std::move(args)) {}
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct Index : public AstNode {
    AstPtr haystack;
    AstPtr needle;

    Index(Source src, AstPtr haystack, AstPtr needle)
        : AstNode(src), haystack(std::move(haystack)), needle(std::move(needle)) {}
    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
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
