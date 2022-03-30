#include <iostream>
#include <variant>
#include <vector>

#include <tao/pegtl.hpp>

#include "gold-common.hpp"

#pragma once


namespace p = tao::pegtl;


namespace Grammar
{
    struct file;
    struct boolean;
    struct identifier;
    struct power;
    struct product;
    struct sum;
    struct ineq;
    struct eq;
    struct conj;
    struct disj;
    struct branch;
    namespace pattern {
        struct ident;
        struct opt_slurp;
        struct def_slurp;
        namespace list {
            struct element;
            struct rule;
        }
        namespace map {
            struct single_entry;
            struct entry;
            struct element;
            struct rule;
        }
    }
    namespace keyword {
        struct Null;
        struct And;
        struct Or;
    }
    namespace postfix {
        struct kwarg_identifier;
        struct kwarg;
        struct posarg;
        struct funcall_operator;
        struct object_access;
        struct subscript_operator;
        struct rule;
    }
    namespace prefix {
        struct rule;
    }
    namespace number {
        struct integer;
        struct floating;
    }
    namespace string {
        struct data;
        struct interp;
        struct post;
    }
    namespace list {
        struct singleton;
        struct splat;
        struct loop;
        struct cond;
        struct rule;
    }
    namespace map {
        struct const_identifier;
        struct var_identifier;
        struct entry;
        struct splat;
        struct loop;
        struct cond;
        struct rule;
    }
    namespace func {
        struct posargs;
        struct kwargs;
        struct rule;
    }
    namespace block {
        struct binding;
        struct rule;
    }
    namespace op {
        struct power;
        struct divide;
        struct idivide;
        struct multiply;
        struct plus;
        struct minus;
        struct le;
        struct ge;
        struct lt;
        struct gt;
        struct dbleq;
        struct ineq;
        struct un_minus;
    }
}


namespace Gold
{

struct Ast
{
    // Normalization functions
    using ExprN = std::function<ExprPtr(const Ast&)>;
    using ModExprN = std::function<ExprPtr(const Ast&, ExprPtr)>;
    using BindingN = std::function<BindingPtr(const Ast&)>;
    using CollectionEltN =std::function<uptr<CollectionElement>(const Ast&)>;
    using FuncallArgN = std::function<void(const Ast&, ExprPtr&)>;
    using ListBindingEltN = std::function<void(const Ast&, uptr<ListBinding>&)>;
    using MapBindingEltN = std::function<void(const Ast&, uptr<MapBinding>&)>;
    using MapBindingLeafN = std::function<MapBindingEntry(const Ast&)>;
    using BlockBindingEltN = std::function<BlockBindingElement(const Ast&)>;

    std::vector<uptr<Ast>> children;
    p::internal::iterator begin;
    p::internal::iterator end;
    std::string name;

    bool is_mapbinding = false;

    std::variant<
        std::monostate,
        ExprN,
        ModExprN,
        BindingN,
        CollectionEltN,
        FuncallArgN,
        ListBindingEltN,
        MapBindingEltN,
        MapBindingLeafN,
        BlockBindingEltN,
        BinaryOperator,
        UnaryOperator
    > normalizer;

    Ast() = default;
    ~Ast() = default;

    Ast( const Ast& ) = delete;
    Ast( Ast&& ) = delete;
    Ast& operator=( const Ast& ) = delete;
    Ast& operator=( Ast&& ) = delete;

    bool is_root() const { return normalizer.index() == 0; }

    template<typename Rule> void set_normalizer() {
        std::cout << "set_normalizer fallback: " << name << std::endl;
    }

    template<typename Rule, typename ParseInput, typename... States>
    void start(const ParseInput& in, States&&...) {
        begin = p::internal::iterator(in.iterator());
    }

    template<typename Rule, typename ParseInput, typename... States>
    void success(const ParseInput& in, States&&...) {
        end = p::internal::iterator(in.iterator());
        name = std::type_index(typeid(Rule)).name();
        set_normalizer<Rule>();
    }

    template<typename Rule, typename ParseInput, typename... States>
    void failure(const ParseInput& in, States&&...) {}

    template<typename Rule, typename ParseInput, typename... States>
    void unwind(const ParseInput&, States&&...) noexcept {}

    template<typename... States>
    void emplace_back(uptr<Ast> child, States&&...) {
        children.push_back(std::move(child));
    }

    Expr* root_expr() const;

    Source source() const;
    std::string_view string_view() const noexcept;
    std::string string() const;
    ExprPtr expr() const;
    ExprPtr postfix(ExprPtr) const;
    void funcall_arg(ExprPtr&) const;
    uptr<CollectionElement> collection_element() const;
    BinaryOperator binop() const;
    UnaryOperator unop() const;
    BindingPtr binding() const;
    BlockBindingElement binding_element() const;
    void list_binding_entry(uptr<ListBinding>& binding) const;
    void map_binding_entry(uptr<MapBinding>& binding) const;
    MapBindingEntry map_binding_leaf() const;
};

template<> void Ast::set_normalizer<Grammar::pattern::ident>();
template<> void Ast::set_normalizer<Grammar::pattern::def_slurp>();
template<> void Ast::set_normalizer<Grammar::pattern::opt_slurp>();
template<> void Ast::set_normalizer<Grammar::pattern::list::element>();
template<> void Ast::set_normalizer<Grammar::pattern::list::rule>();
template<> void Ast::set_normalizer<Grammar::pattern::map::entry>();
template<> void Ast::set_normalizer<Grammar::pattern::map::single_entry>();
template<> void Ast::set_normalizer<Grammar::pattern::map::element>();
template<> void Ast::set_normalizer<Grammar::pattern::map::rule>();
template<> void Ast::set_normalizer<Grammar::file>();
template<> void Ast::set_normalizer<Grammar::boolean>();
template<> void Ast::set_normalizer<Grammar::identifier>();
template<> void Ast::set_normalizer<Grammar::keyword::Null>();
template<> void Ast::set_normalizer<Grammar::number::integer>();
template<> void Ast::set_normalizer<Grammar::number::floating>();
template<> void Ast::set_normalizer<Grammar::string::data>();
template<> void Ast::set_normalizer<Grammar::string::interp>();
template<> void Ast::set_normalizer<Grammar::string::post>();
template<> void Ast::set_normalizer<Grammar::postfix::kwarg_identifier>();
template<> void Ast::set_normalizer<Grammar::postfix::kwarg>();
template<> void Ast::set_normalizer<Grammar::postfix::posarg>();
template<> void Ast::set_normalizer<Grammar::postfix::funcall_operator>();
template<> void Ast::set_normalizer<Grammar::postfix::object_access>();
template<> void Ast::set_normalizer<Grammar::postfix::subscript_operator>();
template<> void Ast::set_normalizer<Grammar::postfix::rule>();
template<> void Ast::set_normalizer<Grammar::prefix::rule>();
template<> void Ast::set_normalizer<Grammar::list::splat>();
template<> void Ast::set_normalizer<Grammar::list::singleton>();
template<> void Ast::set_normalizer<Grammar::list::cond>();
template<> void Ast::set_normalizer<Grammar::list::loop>();
template<> void Ast::set_normalizer<Grammar::list::rule>();
template<> void Ast::set_normalizer<Grammar::map::const_identifier>();
template<> void Ast::set_normalizer<Grammar::map::splat>();
template<> void Ast::set_normalizer<Grammar::map::entry>();
template<> void Ast::set_normalizer<Grammar::map::cond>();
template<> void Ast::set_normalizer<Grammar::map::loop>();
template<> void Ast::set_normalizer<Grammar::map::rule>();
template<> void Ast::set_normalizer<Grammar::block::binding>();
template<> void Ast::set_normalizer<Grammar::block::rule>();
template<> void Ast::set_normalizer<Grammar::func::posargs>();
template<> void Ast::set_normalizer<Grammar::func::kwargs>();
template<> void Ast::set_normalizer<Grammar::func::rule>();
template<> void Ast::set_normalizer<Grammar::branch>();
template<> void Ast::set_normalizer<Grammar::power>();
template<> void Ast::set_normalizer<Grammar::product>();
template<> void Ast::set_normalizer<Grammar::sum>();
template<> void Ast::set_normalizer<Grammar::ineq>();
template<> void Ast::set_normalizer<Grammar::eq>();
template<> void Ast::set_normalizer<Grammar::conj>();
template<> void Ast::set_normalizer<Grammar::disj>();
template<> void Ast::set_normalizer<Grammar::keyword::And>();
template<> void Ast::set_normalizer<Grammar::keyword::Or>();
template<> void Ast::set_normalizer<Grammar::op::power>();
template<> void Ast::set_normalizer<Grammar::op::divide>();
template<> void Ast::set_normalizer<Grammar::op::idivide>();
template<> void Ast::set_normalizer<Grammar::op::multiply>();
template<> void Ast::set_normalizer<Grammar::op::plus>();
template<> void Ast::set_normalizer<Grammar::op::minus>();
template<> void Ast::set_normalizer<Grammar::op::le>();
template<> void Ast::set_normalizer<Grammar::op::ge>();
template<> void Ast::set_normalizer<Grammar::op::lt>();
template<> void Ast::set_normalizer<Grammar::op::gt>();
template<> void Ast::set_normalizer<Grammar::op::dbleq>();
template<> void Ast::set_normalizer<Grammar::op::ineq>();
template<> void Ast::set_normalizer<Grammar::op::un_minus>();

}
