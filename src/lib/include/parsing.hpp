#include <set>
#include <string>

#include <tao/pegtl/contrib/parse_tree.hpp>

#include "gold.hpp"

#pragma once


namespace Gold
{

enum class BinaryOperator {
    plus,
    minus,
    multiply,
    divide,
    integer_divide,
    power,
    less_than,
    less_than_or_eq,
    greater_than,
    greater_than_or_eq,
    equal,
    not_equal,
    conjunction,
    disjunction
};


enum class UnaryOperator {
    negate
};


struct Binding : public Serializable {
    Source src;

    Binding(Source src) : src(src) {}
    virtual ~Binding() {}

    bool bind(EvaluationContext&, Object, bool = true) const;
    virtual bool do_bind(EvaluationContext&, Object) const = 0;

    virtual BindingPtr freeze(EvaluationContext& ctx) const = 0;

    std::pair<std::set<std::string>, std::set<std::string>> free_and_bound() const;
    virtual void free_and_bound(std::set<std::string>&, std::set<std::string>&) const = 0;

    static BindingPtr deserialize(Deserializer&);

    virtual void dump(std::ostream&) const = 0;
    friend std::ostream& operator<<(std::ostream& os, const Binding& binding) { binding.dump(os); return os; }
};


struct IdentifierBinding : public Binding {
    std::string name;

    IdentifierBinding(Source src, std::string name) : Binding(src), name(name) {}
    virtual void dump(std::ostream&) const;
    virtual BindingPtr freeze(EvaluationContext& ctx) const;
    virtual void free_and_bound(std::set<std::string>&, std::set<std::string>&) const;
    virtual bool do_bind(EvaluationContext&, Object) const;
    virtual void do_serialize(Serializer&) const;
};


struct ListBinding : public Binding {
    using Entry = struct Entry {
        BindingPtr binding;
        opt<ExprPtr> fallback = opt<ExprPtr>();
    };

    std::vector<Entry> bindings;
    bool slurp = false;
    opt<std::string> slurp_target;

    ListBinding(Source src) : Binding(src) {}
    ListBinding(Source src, std::vector<Entry> entries, bool slurp, opt<std::string> slurp_target)
        : Binding(src), bindings(std::move(entries)), slurp(slurp), slurp_target(slurp_target) {}

    virtual void dump(std::ostream&) const;
    virtual BindingPtr freeze(EvaluationContext& ctx) const;
    virtual void free_and_bound(std::set<std::string>&, std::set<std::string>&) const;
    virtual bool do_bind(EvaluationContext&, Object) const;
    virtual void do_serialize(Serializer&) const;
};


struct MapBindingEntry {
    std::string name;
    BindingPtr binding;
    opt<ExprPtr> fallback = opt<ExprPtr>();
};


struct MapBinding : public Binding {
    using Entry = MapBindingEntry;

    std::vector<Entry> entries;
    opt<std::string> slurp_target;

    MapBinding(Source src) : Binding(src) {}
    MapBinding(Source src, std::vector<Entry> entries, opt<std::string> slurp_target)
        : Binding(src), entries(std::move(entries)), slurp_target(slurp_target) {}

    virtual void dump(std::ostream&) const;
    virtual BindingPtr freeze(EvaluationContext& ctx) const;
    virtual void free_and_bound(std::set<std::string>&, std::set<std::string>&) const;
    virtual bool do_bind(EvaluationContext&, Object) const;
    virtual void do_serialize(Serializer&) const;
};


struct Expr : public Serializable {
    Source src;

    Expr(Source src) : src(src) {}
    virtual ~Expr() {}

    static uptr<Expr> deserialize(std::string);
    static uptr<Expr> deserialize(std::istream&);
    static uptr<Expr> deserialize(Deserializer&);

    virtual void dump(std::ostream&) const = 0;
    virtual void free_identifiers(std::set<std::string>&) const = 0;
    std::set<std::string> free_identifiers() const;
    virtual Object evaluate(EvaluationContext&) const = 0;

    const Source source() const { return src; }

    std::string dump() const;
    friend std::ostream& operator<<(std::ostream& os, const Expr& node) { node.dump(os); return os; }
};


struct Literal : public Expr {
    const Object object;

    Literal(Source src, Object object) : Expr(src), object(object) {}

    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct Identifier : public Expr {
    const std::string name;

    Identifier(Source src, std::string name) : Expr(src), name(name) {}

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
    ExprPtr node;

    SingletonListElement(ExprPtr node) : node(std::move(node)) {}

    virtual void fill(EvaluationContext&, Object::ListT&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct SplatListElement : public ListElement {
    ExprPtr node;

    SplatListElement(ExprPtr node) : node(std::move(node)) {}

    virtual void fill(EvaluationContext&, Object::ListT&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct CondListElement : public ListElement {
    ExprPtr cond;
    uptr<ListElement> element;

    CondListElement(ExprPtr cond, uptr<ListElement> element)
        : cond(std::move(cond)), element(std::move(element)) {}

    virtual void fill(EvaluationContext&, Object::ListT&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct LoopListElement : public ListElement {
    BindingPtr binding;
    ExprPtr iter;
    uptr<ListElement> element;

    LoopListElement(BindingPtr binding, ExprPtr iter, uptr<ListElement> element)
        : binding(std::move(binding)), iter(std::move(iter)), element(std::move(element)) {}

    virtual void fill(EvaluationContext&, Object::ListT&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct List : public Expr {
    using Entry = struct Entry {
        ExprPtr node;
        bool splat;
    };

    std::vector<uptr<ListElement>> elements;

    List(Source src) : Expr(src) {}
    List(Source src, std::vector<uptr<ListElement>> elements)
        : Expr(src), elements(std::move(elements)) {}

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
    ExprPtr key, node;

    SingletonMapElement(ExprPtr key, ExprPtr node) : key(std::move(key)), node(std::move(node)) {}

    virtual void fill(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct SplatMapElement : public MapElement {
    ExprPtr node;

    SplatMapElement(ExprPtr node) : node(std::move(node)) {}

    virtual void fill(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct CondMapElement : public MapElement {
    ExprPtr cond;
    uptr<MapElement> element;

    CondMapElement(ExprPtr cond, uptr<MapElement> element)
        : cond(std::move(cond)), element(std::move(element)) {}

    virtual void fill(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct LoopMapElement : public MapElement {
    BindingPtr binding;
    ExprPtr iter;
    uptr<MapElement> element;

    LoopMapElement(BindingPtr binding, ExprPtr iter, uptr<MapElement> element)
        : binding(std::move(binding)), iter(std::move(iter)), element(std::move(element)) {}

    virtual void fill(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
    virtual void dump(std::ostream& os) const;
    virtual void free_identifiers(std::set<std::string>&) const;
};


struct Map : public Expr {
    std::vector<uptr<MapElement>> elements;

    Map(Source src) : Expr(src) {}
    Map(Source src, std::vector<uptr<MapElement>> elements)
        : Expr(src), elements(std::move(elements)) {}

    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct BinOp : public Expr {
    ExprPtr lhs, rhs;
    BinaryOperator op;

    BinOp(Source src, ExprPtr l, ExprPtr r, BinaryOperator oper)
        : Expr(src), lhs(std::move(l)), rhs(std::move(r)), op(oper) {}

    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct UnOp : public Expr {
    ExprPtr operand;
    UnaryOperator op;

    UnOp(Source src, ExprPtr operand, UnaryOperator op) : Expr(src), operand(std::move(operand)), op(op) {}

    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct BlockBindingElement {
    BindingPtr binding;
    ExprPtr expression;
};


struct Block : public Expr {
    using BindingElement = BlockBindingElement;

    std::vector<BindingElement> bindings;
    ExprPtr expression;

    Block(Source src) : Expr(src) {}
    Block(Source src, std::vector<BindingElement> bindings, ExprPtr expression)
        : Expr(src), bindings(std::move(bindings)), expression(std::move(expression)) {}

    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct Function : public Expr {
    sptr<Binding> args;
    sptr<Binding> kwargs;
    sptr<Expr> expression;

    Function(Source src) : Expr(src) {}
    Function(Source src, sptr<Binding> args, sptr<Binding> kwargs, sptr<Expr> expression)
        : Expr(src), args(args), kwargs(kwargs), expression(expression) {}

    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct Branch : public Expr {
    ExprPtr condition;
    ExprPtr if_value;
    ExprPtr else_value;

    Branch(Source src, ExprPtr cond, ExprPtr yes, ExprPtr no)
        : Expr(src), condition(std::move(cond)), if_value(std::move(yes)), else_value(std::move(no)) {}

    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct FunCall : public Expr {
    ExprPtr function;
    std::vector<ExprPtr> args;
    std::vector<std::pair<std::string, ExprPtr>> kwargs;

    FunCall(Source src, ExprPtr function) : Expr(src), function(std::move(function)) {}
    FunCall(Source src, ExprPtr function, std::vector<ExprPtr> args, std::vector<std::pair<std::string, ExprPtr>> kwargs)
        : Expr(src), function(std::move(function)), args(std::move(args)), kwargs(std::move(kwargs)) {}

    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


struct Index : public Expr {
    ExprPtr haystack;
    ExprPtr needle;

    Index(Source src, ExprPtr haystack, ExprPtr needle)
        : Expr(src), haystack(std::move(haystack)), needle(std::move(needle)) {}

    virtual void dump(std::ostream&) const;
    virtual void free_identifiers(std::set<std::string>&) const;
    virtual Object evaluate(EvaluationContext&) const;
    virtual void do_serialize(Serializer&) const;
};


template<typename T> ExprPtr parse(T&);

bool analyze_grammar();
ExprPtr parse_string(std::string);
ExprPtr parse_file(std::string);
void debug_parse(std::string);
void debug_parse_tree(std::string);

ExprPtr normalize(tao::pegtl::parse_tree::node&);

} // Namespace Gold
