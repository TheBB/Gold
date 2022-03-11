#include <iostream>
#include <vector>

#include <tao/pegtl.hpp>

#include "gold.hpp"

#pragma once


namespace p = tao::pegtl;


namespace Gold
{

struct Ast
{
    // Normalization functions
    using ExprN = std::function<ExprPtr(const Ast&)>;
    using ModExprN = std::function<ExprPtr(const Ast&, ExprPtr)>;
    using BindingN = std::function<BindingPtr(const Ast&)>;
    using ListEltN =std::function<uptr<ListElement>(const Ast&)>;
    using MapEltN = std::function<uptr<MapElement>(const Ast&)>;
    using ListBindingEltN = std::function<void(const Ast&, uptr<ListBinding>&)>;
    using MapBindingEltN = std::function<void(const Ast&, uptr<MapBinding>&)>;
    using MapBindingLeafN = std::function<MapBinding::Entry(const Ast&)>;
    using BlockBindingEltN = std::function<Block::BindingElement(const Ast&)>;

    std::vector<uptr<Ast>> children;
    p::internal::iterator begin;
    p::internal::iterator end;
    std::string name;

    std::variant<
        std::monostate,
        ExprN,
        ModExprN,
        BindingN,
        ListEltN,
        MapEltN,
        ListBindingEltN,
        MapBindingEltN,
        MapBindingLeafN,
        BlockBindingEltN,
        Operator
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

    Source source() const;
    std::string_view string_view() const noexcept;
    std::string string() const;
    ExprPtr expr() const;
    ExprPtr postfix(ExprPtr expr) const;
    uptr<ListElement> list_element() const;
    uptr<MapElement> map_element() const;
    Operator oper() const;
    BindingPtr binding() const;
    Block::BindingElement binding_element() const;
    void list_binding_entry(uptr<ListBinding>& binding) const;
    void map_binding_entry(uptr<MapBinding>& binding) const;
    MapBinding::Entry map_binding_leaf() const;

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
template<> void Ast::set_normalizer<Grammar::postfix::funcall_operator>();
template<> void Ast::set_normalizer<Grammar::postfix::object_access>();
template<> void Ast::set_normalizer<Grammar::postfix::subscript_operator>();
template<> void Ast::set_normalizer<Grammar::postfix::rule>();
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
template<> void Ast::set_normalizer<Grammar::func::bracketed_param_list>();
template<> void Ast::set_normalizer<Grammar::func::rule>();
template<> void Ast::set_normalizer<Grammar::branch>();
template<> void Ast::set_normalizer<Grammar::product>();
template<> void Ast::set_normalizer<Grammar::sum>();
template<> void Ast::set_normalizer<Grammar::ineq>();
template<> void Ast::set_normalizer<Grammar::eq>();
template<> void Ast::set_normalizer<Grammar::conj>();
template<> void Ast::set_normalizer<Grammar::disj>();
template<> void Ast::set_normalizer<Grammar::keyword::And>();
template<> void Ast::set_normalizer<Grammar::keyword::Or>();
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

}
