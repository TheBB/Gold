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


struct IdentifierBinding : public Binding {
    std::string name;

    IdentifierBinding(Source src, std::string name) : Binding(src), name(name) {}
    virtual void dump(std::ostream&) const;
    virtual BindingPtr freeze(EvaluationContext& ctx) const;
    virtual void binds_identifiers(std::set<std::string>&) const;
    virtual void free_identifiers(std::set<std::string>&) const {}
    virtual bool do_bind(EvaluationContext&, Object) const;
    virtual void do_serialize(Serializer&) const;
};


struct ListBinding : public Binding {
    using Entry = struct Entry {
        BindingPtr binding;
        opt<AstPtr> fallback = opt<AstPtr>();
    };

    std::vector<Entry> bindings;
    bool slurp = false;
    opt<std::string> slurp_target;

    ListBinding(Source src) : Binding(src) {}
    ListBinding(Source src, std::vector<Entry> entries, bool slurp, opt<std::string> slurp_target)
        : Binding(src), bindings(std::move(entries)), slurp(slurp), slurp_target(slurp_target) {}

    virtual void dump(std::ostream&) const;
    virtual BindingPtr freeze(EvaluationContext& ctx) const;
    virtual void binds_identifiers(std::set<std::string>&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual bool do_bind(EvaluationContext&, Object) const;
    virtual void do_serialize(Serializer&) const;
};


struct MapBinding : public Binding {
    using Entry = struct Entry {
        std::string name;
        BindingPtr binding;
        opt<AstPtr> fallback = opt<AstPtr>();
    };

    std::vector<Entry> entries;
    opt<std::string> slurp_target;

    MapBinding(Source src) : Binding(src) {}
    MapBinding(Source src, std::vector<Entry> entries, opt<std::string> slurp_target)
        : Binding(src), entries(std::move(entries)), slurp_target(slurp_target) {}

    virtual void dump(std::ostream&) const;
    virtual BindingPtr freeze(EvaluationContext& ctx) const;
    virtual void binds_identifiers(std::set<std::string>&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual bool do_bind(EvaluationContext&, Object) const;
    virtual void do_serialize(Serializer&) const;
};


struct AstNode : public Serializable {
    Source src;

    AstNode(Source src) : src(src) {}
    virtual ~AstNode() {}

    static uptr<AstNode> deserialize(std::string);
    static uptr<AstNode> deserialize(std::istream&);
    static uptr<AstNode> deserialize(Deserializer&);

    virtual void dump(std::ostream&) const = 0;
    virtual void free_identifiers(std::set<std::string>&) const = 0;
    std::set<std::string> free_identifiers() const;
    virtual Object evaluate(EvaluationContext&) const = 0;

    const Source source() const { return src; }

    std::string dump() const;
    friend std::ostream& operator<<(std::ostream& os, const AstNode& node) { node.dump(os); return os; }
};


struct Literal : public AstNode {
    const Object object;

    Literal(Source src, Object object) : AstNode(src), object(object) {}

    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct Identifier : public AstNode {
    const std::string name;

    Identifier(Source src, std::string name) : AstNode(src), name(name) {}

    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>& idents) const;
    virtual Object evaluate(EvaluationContext& ctx) const;
    virtual void do_serialize(Serializer&) const;
};


struct ListElement : public Serializable {
    virtual ~ListElement() {}
    static uptr<ListElement> deserialize(Deserializer&);

    virtual void fill(EvaluationContext&, Object::ListT&) const = 0;
    virtual void free_identifiers(std::set<std::string>&) const = 0;
    std::set<std::string> free_identifiers() const;

    virtual void dump(std::ostream& os) const = 0;
    friend std::ostream& operator<<(std::ostream& os, const ListElement& node) { node.dump(os); return os; };
};


struct SingletonListElement : public ListElement {
    AstPtr node;

    SingletonListElement(AstPtr node) : node(std::move(node)) {}

    virtual void fill(EvaluationContext&, Object::ListT&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct SplatListElement : public ListElement {
    AstPtr node;

    SplatListElement(AstPtr node) : node(std::move(node)) {}

    virtual void fill(EvaluationContext&, Object::ListT&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct CondListElement : public ListElement {
    AstPtr cond;
    uptr<ListElement> element;

    CondListElement(AstPtr cond, uptr<ListElement> element)
        : cond(std::move(cond)), element(std::move(element)) {}

    virtual void fill(EvaluationContext&, Object::ListT&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct LoopListElement : public ListElement {
    BindingPtr binding;
    AstPtr iter;
    uptr<ListElement> element;

    LoopListElement(BindingPtr binding, AstPtr iter, uptr<ListElement> element)
        : binding(std::move(binding)), iter(std::move(iter)), element(std::move(element)) {}

    virtual void fill(EvaluationContext&, Object::ListT&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct List : public AstNode {
    using Entry = struct Entry {
        AstPtr node;
        bool splat;
    };

    std::vector<uptr<ListElement>> elements;

    List(Source src) : AstNode(src) {}
    List(Source src, std::vector<uptr<ListElement>> elements)
        : AstNode(src), elements(std::move(elements)) {}

    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct MapElement : public Serializable {
    virtual ~MapElement() {}

    virtual void fill(EvaluationContext&) const = 0;
    static uptr<MapElement> deserialize(Deserializer&);
    virtual void free_identifiers(std::set<std::string>&) const = 0;
    std::set<std::string> free_identifiers() const;

    virtual void dump(std::ostream& os) const = 0;
    friend std::ostream& operator<<(std::ostream& os, const MapElement& node) { node.dump(os); return os; };
};


struct SingletonMapElement : public MapElement {
    AstPtr key, node;

    SingletonMapElement(AstPtr key, AstPtr node) : key(std::move(key)), node(std::move(node)) {}

    virtual void fill(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct SplatMapElement : public MapElement {
    AstPtr node;

    SplatMapElement(AstPtr node) : node(std::move(node)) {}

    virtual void fill(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct CondMapElement : public MapElement {
    AstPtr cond;
    uptr<MapElement> element;

    CondMapElement(AstPtr cond, uptr<MapElement> element)
        : cond(std::move(cond)), element(std::move(element)) {}

    virtual void fill(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct LoopMapElement : public MapElement {
    BindingPtr binding;
    AstPtr iter;
    uptr<MapElement> element;

    LoopMapElement(BindingPtr binding, AstPtr iter, uptr<MapElement> element)
        : binding(std::move(binding)), iter(std::move(iter)), element(std::move(element)) {}

    virtual void fill(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct Map : public AstNode {
    std::vector<uptr<MapElement>> elements;

    Map(Source src) : AstNode(src) {}
    Map(Source src, std::vector<uptr<MapElement>> elements)
        : AstNode(src), elements(std::move(elements)) {}

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
    using BindingElement = struct Entry {
        BindingPtr binding;
        AstPtr expression;
    };

    std::vector<BindingElement> bindings;
    AstPtr expression;

    Block(Source src) : AstNode(src) {}
    Block(Source src, std::vector<BindingElement> bindings, AstPtr expression)
        : AstNode(src), bindings(std::move(bindings)), expression(std::move(expression)) {}

    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct Function : public AstNode {
    std::vector<BindingPtr> parameters;
    sptr<AstNode> expression;

    Function(Source src) : AstNode(src) {}
    Function(Source src, std::vector<BindingPtr> parameters, sptr<AstNode> expression)
        : AstNode(src), parameters(std::move(parameters)), expression(expression) {}

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
        : AstNode(src), condition(std::move(cond)), if_value(std::move(yes)), else_value(std::move(no)) {}

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


} // Namespace Gold
