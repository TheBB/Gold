#include <cinttypes>
#include <iostream>
#include <string>

#include <fmt/core.h>

#include <tao/pegtl/contrib/parse_tree.hpp>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;
namespace p = tao::pegtl;


template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


static std::string operator_to_string(Operator op) {
    switch (op) {
    case Operator::plus: return "+";
    case Operator::minus: return "-";
    case Operator::multiply: return "*";
    case Operator::divide: return "/";
    case Operator::integer_divide: return "//";
    case Operator::less_than: return "<";
    case Operator::less_than_or_eq: return "<=";
    case Operator::greater_than: return ">";
    case Operator::greater_than_or_eq: return ">=";
    case Operator::equal: return "==";
    case Operator::not_equal: return "!=";
    case Operator::conjunction: return "and";
    default: return "or";
    }
}


static Operator operator_from_string(std::string value) {
    if (value == "+") return Operator::plus;
    if (value == "-") return Operator::minus;
    if (value == "*") return Operator::multiply;
    if (value == "/") return Operator::divide;
    if (value == "//") return Operator::integer_divide;
    if (value == "<") return Operator::less_than;
    if (value == "<=") return Operator::less_than_or_eq;
    if (value == ">") return Operator::greater_than;
    if (value == ">=") return Operator::greater_than_or_eq;
    if (value == "==") return Operator::equal;
    if (value == "!=") return Operator::not_equal;
    if (value == "and") return Operator::conjunction;
    return Operator::disjunction;
}


bool Binding::bind(EvaluationContext& ctx, Object obj, bool autocollapse) const {
    ctx.push_namespace();
    auto retval = do_bind(ctx, obj);
    if (autocollapse)
        ctx.collapse_namespace();
    return retval;
}


std::set<std::string> Binding::binds_identifiers() const {
    std::set<std::string> retval;
    binds_identifiers(retval);
    return retval;
}


std::set<std::string> Binding::free_identifiers() const {
    std::set<std::string> retval;
    free_identifiers(retval);
    return retval;
}


void IdentifierBinding::dump(std::ostream& os) const {
    os << "Id(" << name << ")";
}


BindingPtr IdentifierBinding::freeze(EvaluationContext&) const {
    return std::make_unique<IdentifierBinding>(src, name);
}


void IdentifierBinding::binds_identifiers(std::set<std::string>& idents) const {
    idents.insert(name);
}


bool IdentifierBinding::do_bind(EvaluationContext& ctx, Object obj) const {
    ctx.assign(name, obj);
    return true;
}


void ListBinding::dump(std::ostream& os) const {
    os << "List(";
    bool first = true;
    for (auto& binding : bindings) {
        if (!first)
            os << ", ";
        os << "Entry(";
        binding.binding->dump(os);
        if (binding.fallback.has_value())
            os << ", " << *binding.fallback.value();
        os << ")";
        first = false;
    }
    if (slurp) {
        if (!first)
            os << ", ";
        os << "...";
        if (slurp_target.has_value())
            os << slurp_target.value();
    }
    os << ")";
}


BindingPtr ListBinding::freeze(EvaluationContext& ctx) const {
    auto retval = std::make_unique<ListBinding>(src);
    retval->slurp = slurp;
    retval->slurp_target = slurp_target;
    for (auto& entry : bindings)
        retval->bindings.push_back(ListBinding::Entry {
            entry.binding->freeze(ctx),
            entry.fallback.has_value() ?
                std::make_unique<Literal>(
                    entry.fallback.value()->source(),
                    entry.fallback.value()->evaluate(ctx)
                ) : opt<AstPtr>()
        });
    return retval;
}


void ListBinding::binds_identifiers(std::set<std::string>& idents) const {
    for (auto& binding : bindings)
        binding.binding->binds_identifiers(idents);
    if (slurp_target.has_value())
        idents.insert(slurp_target.value());
}


void ListBinding::free_identifiers(std::set<std::string>& idents) const {
    for (auto& binding : bindings) {
        if (binding.fallback.has_value())
            binding.fallback.value()->free_identifiers(idents);
        binding.binding->free_identifiers(idents);
    }
}


bool ListBinding::do_bind(EvaluationContext& ctx, Object obj) const {
    if (obj.type() != Object::Type::list)
        return false;
    auto& list = obj.unsafe_list();

    if (list->size() > bindings.size() && !slurp)
        return false;

    size_t i = 0;
    for (; i < bindings.size(); i++) {
        Object value;
        if (i >= list->size()) {
            if (bindings[i].fallback.has_value())
                value = bindings[i].fallback.value()->evaluate(ctx);
            else
                return false;
        }
        else
            value = list->at(i);

        if (!bindings[i].binding->do_bind(ctx, value))
            return false;
    }

    if (!slurp || !slurp_target.has_value())
        return true;

    Object::ListT objs;
    for (; i < list->size(); i++)
        objs.push_back(list->at(i));
    ctx.assign(slurp_target.value(), Object::list(std::move(objs)));

    return true;
}


void MapBinding::dump(std::ostream& os) const {
    os << "Map(";
    bool first = true;
    for (auto& entry : entries) {
        if (!first)
            os << ", ";
        os << "Entry(" << entry.name << ", " << *entry.binding;
        if (entry.fallback.has_value())
            os << ", " << *entry.fallback.value();
        os << ")";
        first = false;
    }
    if (slurp_target) {
        if (!first)
            os << ", ";
        os << "..." << slurp_target.value();
    }
    os << ")";
}


BindingPtr MapBinding::freeze(EvaluationContext& ctx) const {
    auto retval = std::make_unique<MapBinding>(src);
    retval->slurp_target = slurp_target;
    for (auto& entry : entries)
        retval->entries.push_back(MapBinding::Entry {
            entry.name,
            entry.binding->freeze(ctx),
            entry.fallback.has_value() ?
                std::make_unique<Literal>(
                    entry.fallback.value()->source(),
                    entry.fallback.value()->evaluate(ctx)
                ) : opt<AstPtr>()
        });
    return retval;
}


void MapBinding::binds_identifiers(std::set<std::string>& idents) const {
    for (auto& entry : entries)
        entry.binding->binds_identifiers(idents);
    if (slurp_target.has_value())
        idents.insert(slurp_target.value());
}


void MapBinding::free_identifiers(std::set<std::string>& idents) const {
    for (auto& entry : entries) {
        if (entry.fallback.has_value())
            entry.fallback.value()->free_identifiers(idents);
        entry.binding->free_identifiers(idents);
    }
}


bool MapBinding::do_bind(EvaluationContext& ctx, Object obj) const {
    if (obj.type() != Object::Type::map)
        return false;
    const auto& map = obj.unsafe_map();

    for (auto& entry : entries) {
        auto it = map->find(entry.name);
        Object value;

        if (it == map->end()) {
            if (entry.fallback.has_value())
                value = entry.fallback.value()->evaluate(ctx);
            else
                return false;
        }
        else
            value = it->second;

        if (!entry.binding->do_bind(ctx, value))
            return false;
    }

    if (!slurp_target.has_value())
        return true;

    Object::MapT newmap(*map);
    for (auto& entry : entries)
        newmap.erase(entry.name);
    ctx.assign(slurp_target.value(), Object::map(std::move(newmap)));

    return true;
}


std::string Gold::AstNode::dump() const {
    std::stringstream ss;
    ss << *this;
    return ss.str();
}


std::set<std::string> AstNode::free_identifiers() const {
    std::set<std::string> idents;
    free_identifiers(idents);
    return idents;
}


void Literal::dump(std::ostream& os) const {
    os << "Lit(" << object << ")";
}


void Literal::free_identifiers(std::set<std::string>&) const {}


Object Literal::evaluate(EvaluationContext&) const {
    return object;
}


void Identifier::dump(std::ostream& os) const {
    os << "Id(" << name << ")";
}


void Identifier::free_identifiers(std::set<std::string>& idents) const {
    idents.insert(name);
}


Object Identifier::evaluate(EvaluationContext& ctx) const {
    try {
        return ctx.lookup(name);
    }
    catch (EvalException& e) {
        e.tag_position(source());
        throw;
    }
}


std::set<std::string> ListElement::free_identifiers() const {
    std::set<std::string> idents;
    free_identifiers(idents);
    return idents;
}


void SingletonListElement::fill(EvaluationContext& ctx, Object::ListT& list) const {
    list.push_back(node->evaluate(ctx));
}


void SingletonListElement::free_identifiers(std::set<std::string>& idents) const {
    node->free_identifiers(idents);
}


void SingletonListElement::dump(std::ostream& os) const {
    os << *node;
}


void SplatListElement::fill(EvaluationContext& ctx, Object::ListT& list) const {
    auto val = node->evaluate(ctx);
    if (val.type() != Object::Type::list)
        throw EvalException(node->source(), fmt::format("unable to splat non-list: `{}`", val.type_name()));
    auto& inlist = val.unsafe_list();
    std::copy(inlist->begin(), inlist->end(), std::back_inserter(list));
}


void SplatListElement::free_identifiers(std::set<std::string>& idents) const {
    node->free_identifiers(idents);
}


void SplatListElement::dump(std::ostream& os) const {
    os << "Splat(" << *node << ")";
}


void CondListElement::fill(EvaluationContext& ctx, Object::ListT& list) const {
    auto c = cond->evaluate(ctx);
    if (c.type() != Object::Type::boolean)
        throw EvalException(
            cond->source(),
            fmt::format("attempted branching with non-boolean type `{}`", c.type_name())
        );
    if (c.unsafe_boolean())
        element->fill(ctx, list);
}


void CondListElement::free_identifiers(std::set<std::string>& idents) const {
    cond->free_identifiers(idents);
    element->free_identifiers(idents);
}


void CondListElement::dump(std::ostream& os) const {
    os << "Cond(" << *cond << ", " << *element << ")";
}


void LoopListElement::fill(EvaluationContext& ctx, Object::ListT& list) const {
    auto val = iter->evaluate(ctx);
    if (val.type() != Object::Type::list)
        throw EvalException(
            iter->source(),
            fmt::format("unable to iterate over non-list `{}`", val.type_name())
        );
    ctx.push_namespace();
    for (auto& v : *val.unsafe_list()) {
        if (!binding->bind(ctx, v))
            throw EvalException(binding->src, "failed to bind pattern");
        element->fill(ctx, list);
    }
    ctx.pop_namespace();
}


void LoopListElement::free_identifiers(std::set<std::string>& idents) const {
    iter->free_identifiers(idents);
    binding->free_identifiers(idents);
    auto newly_bound = binding->binds_identifiers();
    auto candidates = element->free_identifiers();
    for (auto& p : newly_bound)
        candidates.erase(p);
    for (auto& c : candidates)
        idents.insert(c);
}


void LoopListElement::dump(std::ostream& os) const {
    os << "For(" << *binding << ", " << *iter << ", " << *element << ")";
}


void List::dump(std::ostream& os) const {
    os << "List(";
    bool first = true;
    for (auto& element : elements) {
        if (!first)
            os << ", ";
        element->dump(os);
        first = false;
    }
    os << ")";
}


void List::free_identifiers(std::set<std::string>& idents) const {
    for (auto& element : elements)
        element->free_identifiers(idents);
}


Object List::evaluate(EvaluationContext& ctx) const {
    std::vector<Object> objs;
    for (auto& entry : elements)
        entry->fill(ctx, objs);
    return Object::list(std::move(objs));
}


std::set<std::string> MapElement::free_identifiers() const {
    std::set<std::string> idents;
    free_identifiers(idents);
    return idents;
}


void SingletonMapElement::fill(EvaluationContext& ctx) const {
    auto k = key->evaluate(ctx);
    if (k.type() != Object::Type::string)
        throw EvalException(
            key->source(),
            fmt::format("attempted using non-string type `{}` as object key", k.type_name())
        );
    ctx.assign_object(k.unsafe_string(), node->evaluate(ctx));
}


void SingletonMapElement::free_identifiers(std::set<std::string>& idents) const {
    key->free_identifiers(idents);
    node->free_identifiers(idents);
}


void SingletonMapElement::dump(std::ostream& os) const {
    os << "Entry(" << *key << ", " << *node << ")";
}


void SplatMapElement::fill(EvaluationContext& ctx) const {
    auto val = node->evaluate(ctx);
    if (val.type() != Object::Type::map)
        throw EvalException(node->source(), fmt::format("unable to splat non-map: `{}`", val.type_name()));
    for (auto& [key, val] : *val.unsafe_map())
        ctx.assign_object(key, val);
}


void SplatMapElement::free_identifiers(std::set<std::string>& idents) const {
    node->free_identifiers(idents);
}


void SplatMapElement::dump(std::ostream& os) const {
    os << "Splat(" << *node << ")";
}


void CondMapElement::fill(EvaluationContext& ctx) const {
    auto c = cond->evaluate(ctx);
    if (c.type() != Object::Type::boolean)
        throw EvalException(
            cond->source(),
            fmt::format("attempted branching with non-boolean type `{}`", c.type_name())
        );
    if (c.unsafe_boolean())
        element->fill(ctx);
}


void CondMapElement::free_identifiers(std::set<std::string>& idents) const {
    cond->free_identifiers(idents);
    element->free_identifiers(idents);
}


void CondMapElement::dump(std::ostream& os) const {
    os << "Cond(" << *cond << ", " << *element << ")";
}


void LoopMapElement::fill(EvaluationContext& ctx) const {
    auto val = iter->evaluate(ctx);
    if (val.type() != Object::Type::list)
        throw EvalException(
            iter->source(),
            fmt::format("unable to iterate over non-list `{}`", val.type_name())
        );
    ctx.push_namespace();
    for (auto& v : *val.unsafe_list()) {
        if (!binding->bind(ctx, v))
            throw EvalException(binding->src, "failed to bind pattern");
        element->fill(ctx);
    }
    ctx.pop_namespace();
}


void LoopMapElement::free_identifiers(std::set<std::string>& idents) const {
    iter->free_identifiers(idents);
    binding->free_identifiers(idents);
    auto newly_bound = binding->binds_identifiers();
    auto candidates = element->free_identifiers();
    for (auto& p : newly_bound)
        candidates.erase(p);
    for (auto& c : candidates)
        idents.insert(c);
}


void LoopMapElement::dump(std::ostream& os) const {
    os << "For(" << *binding << ", " << *iter << ", " << *element << ")";
}


void Map::dump(std::ostream& os) const {
    os << "Map(";
    bool first = true;
    for (auto& element : elements) {
        if (!first)
            os << ", ";
        element->dump(os);
        first = false;
    }
    os << ")";
}


void Map::free_identifiers(std::set<std::string>& idents) const {
    for (auto& element : elements)
        element->free_identifiers(idents);
}


Object Map::evaluate(EvaluationContext& ctx) const {
    ctx.push_object();
    for (auto& element : elements)
        element->fill(ctx);
    return ctx.finalize_object();
}


void BinOp::dump(std::ostream& os) const {
    os << "BinOp(" << *lhs << " " << operator_to_string(op) << " " <<  *rhs << ")";
}


void BinOp::free_identifiers(std::set<std::string>& idents) const {
    lhs->free_identifiers(idents);
    rhs->free_identifiers(idents);
}


Object BinOp::evaluate(EvaluationContext& ctx) const {
    auto l = lhs->evaluate(ctx);
    try {
        if (op == Operator::conjunction)
            return (bool)l ? rhs->evaluate(ctx) : l;
        if (op == Operator::disjunction)
            return (bool)l ? l : rhs->evaluate(ctx);

        auto r = rhs->evaluate(ctx);
        switch (op) {
        case Operator::plus: return l + r; break;
        case Operator::minus: return l - r; break;
        case Operator::multiply: return l * r; break;
        case Operator::divide: return l / r; break;
        case Operator::integer_divide: return l.operator_idiv(r); break;
        case Operator::less_than: return Object::boolean(l < r); break;
        case Operator::less_than_or_eq: return Object::boolean(l <= r); break;
        case Operator::greater_than: return Object::boolean(l > r); break;
        case Operator::greater_than_or_eq: return Object::boolean(l >= r); break;
        case Operator::equal: return Object::boolean(l == r); break;
        default: return Object::boolean(l != r); break;
        }
    }
    catch (EvalException& e) {
        e.tag_position(source());
        throw;
    }
}


void Block::dump(std::ostream& os) const {
    os << "Block(";
    bool first = true;
    for (auto& [binding, value] : bindings) {
        if (!first)
            os << ", ";
        os << "Entry(" << *binding << ", " << *value << ")";
        first = false;
    }
    if (!first)
        os << ", ";
    os << *expression << ")";
}


void Block::free_identifiers(std::set<std::string>& idents) const {
    std::set<std::string> bound;
    for (auto& [binding, val] : bindings) {
        for (auto& c : val->free_identifiers()) {
            if (bound.find(c) == bound.end())
                idents.insert(c);
        }
        for (auto& c : binding->free_identifiers()) {
            if (bound.find(c) == bound.end())
                idents.insert(c);
        }
        for (auto& name : binding->binds_identifiers())
            bound.insert(name);
    }
    for (auto& c : expression->free_identifiers()) {
        if (bound.find(c) == bound.end())
            idents.insert(c);
    }
}


Object Block::evaluate(EvaluationContext& ctx) const {
    ctx.push_namespace();
    for (auto& [binding, value] : bindings) {
        if (!binding->bind(ctx, value->evaluate(ctx))) {
            ctx.pop_namespace();
            throw EvalException(binding->src, "failed to bind pattern");
        }
    }
    auto retval = expression->evaluate(ctx);
    ctx.pop_namespace();
    return retval;
}


void Function::dump(std::ostream& os) const {
    os << "Function(";
    bool first = true;
    for (auto& p : *parameters) {
        if (!first)
            os << ", ";
        os << *p;
        first = false;
    }
    if (!first)
        os << ", ";
    os << *expression << ")";
}


void Function::free_identifiers(std::set<std::string>& idents) const {
    auto candidates = expression->free_identifiers();
    for (auto& p : *parameters) {
        p->free_identifiers(idents);
        auto bound = p->binds_identifiers();
        for (auto& c : bound)
            candidates.erase(c);
    }
    for (auto& c : candidates)
        idents.insert(c);
}


Object Function::evaluate(EvaluationContext& ctx) const {
    auto free = AstNode::free_identifiers();
    auto closure = std::make_shared<Object::ClosureT>();

    try {
        for (auto& id : free)
            closure->nonlocals[id] = ctx.lookup(id);
        closure->parameters = std::make_shared<std::vector<BindingPtr>>();
        for (auto& parameter : *parameters)
            closure->parameters->push_back(parameter->freeze(ctx));
    }
    catch (EvalException& e) {
        e.tag_position(source());
        throw;
    }

    closure->expression = expression;
    return Object::closure(closure);
}


void Branch::dump(std::ostream& os) const {
    os << "Branch(" << *condition << ", " << *if_value << ", " << *else_value << ")";
}


void Branch::free_identifiers(std::set<std::string>& idents) const {
    condition->free_identifiers(idents);
    if_value->free_identifiers(idents);
    else_value->free_identifiers(idents);
}


Object Branch::evaluate(EvaluationContext& ctx) const {
    auto cond = condition->evaluate(ctx);
    if (cond.type() != Object::Type::boolean)
        throw EvalException(
            condition->source(),
            fmt::format("attempted branching with non-boolean type `{}`", cond.type_name())
        );
    if (cond.unsafe_boolean())
        return if_value->evaluate(ctx);
    return else_value->evaluate(ctx);
}


void FunCall::dump(std::ostream& os) const {
    os << "FunCall(" << *function;
    for (auto& arg : args)
        os << ", " << *arg;
    os << ")";
}


void FunCall::free_identifiers(std::set<std::string>& idents) const {
    function->free_identifiers(idents);
    for (auto& arg : args)
        arg->free_identifiers(idents);
}


Object FunCall::evaluate(EvaluationContext& ctx) const {
    auto func = function->evaluate(ctx);
    std::vector<Object> arglist;
    for (auto& arg : args)
        arglist.push_back(arg->evaluate(ctx));
    try {
        auto rval = func(ctx, arglist);
        return rval;
    }
    catch (EvalException& e) {
        e.tag_position(source(), true);
        throw;
    }
}


void Index::dump(std::ostream& os) const {
    os << "Index(" << *haystack << ", " << *needle << ")";
}


void Index::free_identifiers(std::set<std::string>& idents) const {
    haystack->free_identifiers(idents);
    needle->free_identifiers(idents);
}


Object Index::evaluate(EvaluationContext& ctx) const {
    auto container = haystack->evaluate(ctx);
    auto index = needle->evaluate(ctx);
    try {
        return container[index];
    }
    catch (EvalException& e) {
        e.tag_position(source());
        throw;
    }
}


static Source source(p::parse_tree::node& node) {
    auto src = node.begin();
    return Source { src.byte, src.line, src.column };
}


template<typename T>
static std::string codepoint_as_string(T it, int nchars) {
    uint16_t codepoint = 0;
    for (int i = 0; i < nchars; i++) {
        codepoint *= 16;
        char s = it[i + 1];
        if ('A' <= s && s <= 'F')
            codepoint += s - 'A' + 10;
        else if ('a' <= s && s <= 'f')
            codepoint += s - 'a' + 10;
        else
            codepoint += s - '0';
    }

    if (codepoint < 128) {
        char a = codepoint & 0b0111'1111;
        return std::string{a};
    }
    else if (codepoint < 2048) {
        char a = ((codepoint & 0b0000'0111'1100'0000) >> 6) | 0b1100'0000;
        char b = ((codepoint & 0b0000'0000'0011'1111) >> 0) | 0b1000'0000;
        return std::string{a,b};
    }

    char a = ((codepoint & 0b1111'0000'0000'0000) >> 12) | 0b1110'0000;
    char b = ((codepoint & 0b0000'1111'1100'0000) >>  6) | 0b1000'0000;
    char c = ((codepoint & 0b0000'0000'0011'1111) >>  0) | 0b1000'0000;
    return std::string{a,b,c};
}


static std::string nodetype(p::parse_tree::node& node) {
    std::string type(node.type);
    if (type.substr(0, 6) == "struct")
        type = type.substr(7);
    return type;
}


static AstPtr normalize_map_identifier(p::parse_tree::node& node) {
    auto type = nodetype(node);

    if (type == "Grammar::map::const_identifier")
        return std::make_unique<Literal>(source(node), Object::string(node.string()));
    else
        return normalize(*node.children[0]);
}


static BindingPtr normalize_binding(p::parse_tree::node& node);


static MapBinding::Entry normalize_map_binding_element(p::parse_tree::node& node) {
    if (nodetype(node) == "Grammar::pattern::map::entry")
       return MapBinding::Entry {
            node.children[0]->string(),
            normalize_binding(*node.children[1])
        };

    return MapBinding::Entry {
        node.children[0]->string(),
        std::make_unique<IdentifierBinding>(source(*node.children[0]), node.children[0]->string())
    };
}


static BindingPtr normalize_binding(p::parse_tree::node& node) {
    auto type = nodetype(node);
    auto src = source(node);

    if (type == "Grammar::pattern::ident")
        return std::make_unique<IdentifierBinding>(src, node.string());

    else if (type == "Grammar::pattern::list::rule") {
        auto list = std::make_unique<ListBinding>(src);
        for (auto& c : node.children) {
            if (nodetype(*c) == "Grammar::pattern::opt_slurp") {
                list->slurp = true;
                if (c->children.size() > 0)
                    list->slurp_target = c->children[0]->string();
            }
            else {
                auto element = ListBinding::Entry { normalize_binding(*c->children[0]) };
                if (c->children.size() > 1)
                    element.fallback = normalize(*c->children[1]);
                list->bindings.push_back(std::move(element));
            }
        }
        return list;
    }

    else if (type == "Grammar::pattern::map::rule") {
        auto map = std::make_unique<MapBinding>(src);
        for (auto& c : node.children) {
            if (nodetype(*c) == "Grammar::pattern::def_slurp")
                map->slurp_target = c->children[0]->string();
            else {
                auto element = normalize_map_binding_element(*c->children[0]);
                if (c->children.size() > 1)
                    element.fallback = normalize(*c->children[1]);
                map->entries.push_back(std::move(element));
            }
        }
        return map;
    }

    throw EvalException(fmt::format("normalize_binding: unknown binding: {}", type));
}


static uptr<ListElement> normalize_list_element(p::parse_tree::node& node) {
    auto type = nodetype(node);

    if (type == "Grammar::splatted")
        return std::make_unique<SplatListElement>(normalize(*node.children[0]));

    else if (type == "Grammar::list::loop")
        return std::make_unique<LoopListElement>(
            normalize_binding(*node.children[0]),
            normalize(*node.children[1]),
            normalize_list_element(*node.children[2])
        );

    else if (type == "Grammar::list::cond")
        return std::make_unique<CondListElement>(
            normalize(*node.children[0]),
            normalize_list_element(*node.children[1])
        );

    else
        return std::make_unique<SingletonListElement>(normalize(node));
}


static uptr<MapElement> normalize_map_element(p::parse_tree::node& node) {
    auto type = nodetype(node);

    if (type == "Grammar::splatted")
        return std::make_unique<SplatMapElement>(normalize(*node.children[0]));

    else if (type == "Grammar::map::loop")
        return std::make_unique<LoopMapElement>(
            normalize_binding(*node.children[0]),
            normalize(*node.children[1]),
            normalize_map_element(*node.children[2])
        );

    else if (type == "Grammar::map::cond")
        return std::make_unique<CondMapElement>(
            normalize(*node.children[0]),
            normalize_map_element(*node.children[1])
        );

    else
        return std::make_unique<SingletonMapElement>(
            normalize_map_identifier(*node.children[0]),
            normalize(*node.children[1])
        );
}


AstPtr Gold::normalize(p::parse_tree::node& node) {
    if (node.is_root())
        return normalize(*node.children[0]);

    auto type = nodetype(node);

    if (type == "Grammar::file") {
        return normalize(*node.children[0]);
    }

    else if (type == "Grammar::boolean") {
        Object obj = Object::boolean(node.string_view() == "true");
        return std::make_unique<Literal>(Literal {{source(node)}, obj});
    }

    else if (type == "Grammar::number::rule") {
        auto& c = node.children[0];

        if (nodetype(*c) == "Grammar::number::integer") {
            auto str = node.string();
            auto value = std::strtoimax(str.c_str(), nullptr, 10);
            return std::make_unique<Literal>(source(node), Object::integer(value));
        }
        else {
            auto str = node.string();
            auto value = std::stod(str);
            return std::make_unique<Literal>(source(node), Object::floating(value));
        }
    }

    else if (type == "Grammar::string::data") {
        auto data = node.string_view();
        std::stringstream builder;
        for (auto it = data.begin(); it != data.end(); it++) {
            if (*it == '\\') {
                it++;
                switch (*it) {
                case 'u': {
                    builder << codepoint_as_string(it, 4);
                    it += 4;
                    break;
                }
                case 'b': builder << '\b'; break;
                case 'f': builder << '\f'; break;
                case 'n': builder << '\n'; break;
                case 'r': builder << '\r'; break;
                case 't': builder << '\t'; break;
                default: builder << *it; break;
                }
            }
            else
                builder << *it;
        }
        Object obj = Object::string(builder.str());
        return std::make_unique<Literal>(source(node), obj);
    }

    else if (type == "Grammar::string::interp") {
        auto func = std::make_unique<Identifier>(source(node), "str");
        auto call = std::make_unique<FunCall>(source(node), std::move(func));
        call->args.push_back(normalize(*node.children[0]));
        return call;
    }

    else if (type == "Grammar::string::post") {
        if (node.children.size() == 0)
            return std::make_unique<Literal>(source(node), Object::string(""));
        auto ast = normalize(*node.children[0]);
        auto it = node.children.begin();
        while (++it != node.children.end()) {
            auto rhs = normalize(**it);
            ast = std::make_unique<BinOp>(source(**it), std::move(ast), std::move(rhs), Operator::plus);
        }
        return ast;
    }

    else if (type == "Grammar::keyword::Null") {
        return std::make_unique<Literal>(source(node), Object::null());
    }

    else if (type == "Grammar::identifier") {
        return std::make_unique<Identifier>(source(node), node.string());
    }

    else if (type == "Grammar::list::rule") {
        auto list = std::make_unique<List>(source(node));
        for (auto&& c : node.children)
            list->elements.push_back(normalize_list_element(*c));
        return list;
    }

    else if (type == "Grammar::map::rule") {
        auto map = std::make_unique<Map>(source(node));
        for (auto&& c : node.children)
            map->elements.push_back(normalize_map_element(*c));
        return map;
    }

    else if (type.substr(0, 15) == "Grammar::rbinop") {
        if (node.children.size() == 1)
            return normalize(*node.children[0]);
        return std::make_unique<BinOp>(
            source(*node.children[1]),
            normalize(*node.children[0]),
            normalize(*node.children[2]),
            operator_from_string(node.children[1]->string())
        );
    }

    else if (type.substr(0, 15) == "Grammar::lbinop") {
        auto it = node.children.begin();
        auto ast = normalize(**it++);
        while (it != node.children.end()) {
            auto src = source(**it);
            auto op = operator_from_string((*it++)->string());
            ast = std::make_unique<BinOp>(src, std::move(ast), normalize(**it++), op);
        }
        return ast;
    }

    else if (type == "Grammar::block::rule") {
        auto block = std::make_unique<Block>(source(node));
        for (auto&& c : node.children) {
            if (nodetype(*c) == "Grammar::block::binding")
                block->bindings.push_back({
                    normalize_binding(*c->children[0]),
                    normalize(*c->children[1])
                });
            else
                block->expression = normalize(*c);
        }
        return block;
    }

    else if (type == "Grammar::func::rule") {
        auto function = std::make_unique<Function>(source(node));
        for (auto&& c : node.children[0]->children)
            function->parameters->push_back(normalize_binding(*c));
        function->expression = normalize(*node.children[1]);
        return function;
    }

    else if (type == "Grammar::branch")
        return std::make_unique<Branch>(
            source(node),
            normalize(*node.children[0]),
            normalize(*node.children[1]),
            normalize(*node.children[2])
        );

    else if (type == "Grammar::postfix::rule") {
        auto it = node.children.begin();
        auto value = normalize(**it++);
        while (it != node.children.end()) {
            auto stype = nodetype(**it);
            if (stype == "Grammar::postfix::funcall_operator") {
                auto funcall = std::make_unique<FunCall>(source(**it), std::move(value));
                for (auto&& c : (*it)->children)
                    funcall->args.push_back(normalize(*c));
                value = std::move(funcall);
            }
            else if (stype == "Grammar::postfix::object_access") {
                auto field = Object::string((*it)->children[0]->string());
                auto index = std::make_unique<Index>(
                    source(**it),
                    std::move(value),
                    std::make_unique<Literal>(source(**it), field)
                );
                value = std::move(index);
            }
            else if (stype == "Grammar::postfix::subscript_operator") {
                auto index = std::make_unique<Index>(
                    source(**it),
                    std::move(value),
                    normalize(*(*it)->children[0])
                );
                value = std::move(index);
            }
            it++;
        }
        return value;
    }

    throw EvalException(fmt::format("normalize: unknown node: {}", type));
}
