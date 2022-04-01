#include <cinttypes>
#include <iostream>
#include <string>

#include <fmt/core.h>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;


template<class... Ts> struct overloaded : Ts... { using Ts::operator()...; };
template<class... Ts> overloaded(Ts...) -> overloaded<Ts...>;


static std::string binop_to_string(BinaryOperator op) {
    switch (op) {
    case BinaryOperator::plus: return "+";
    case BinaryOperator::minus: return "-";
    case BinaryOperator::multiply: return "*";
    case BinaryOperator::divide: return "/";
    case BinaryOperator::integer_divide: return "//";
    case BinaryOperator::power: return "^";
    case BinaryOperator::less_than: return "<";
    case BinaryOperator::less_than_or_eq: return "<=";
    case BinaryOperator::greater_than: return ">";
    case BinaryOperator::greater_than_or_eq: return ">=";
    case BinaryOperator::equal: return "==";
    case BinaryOperator::not_equal: return "!=";
    case BinaryOperator::conjunction: return "and";
    default: return "or";
    }
}


static std::string unop_to_string(UnaryOperator op) {
    switch (op) {
    default: return "-";
    }
}


bool Binding::bind(EvaluationContext& ctx, Object obj, bool autocollapse) const {
    ctx.push_namespace();
    auto retval = do_bind(ctx, obj);
    if (autocollapse)
        ctx.collapse_namespace();
    return retval;
}


std::pair<std::set<std::string>, std::set<std::string>> Binding::free_and_bound() const {
    std::set<std::string> free, bound;
    free_and_bound(free, bound);
    return std::pair(free, bound);
}


void IdentifierBinding::dump(std::ostream& os) const {
    os << "Id(" << name << ")";
}


BindingPtr IdentifierBinding::freeze(EvaluationContext&) const {
    return std::make_unique<IdentifierBinding>(src, name);
}


void IdentifierBinding::free_and_bound(std::set<std::string>&, std::set<std::string>& bound) const {
    bound.insert(name);
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
                ) : opt<ExprPtr>()
        });
    return retval;
}


void ListBinding::free_and_bound(std::set<std::string>& free, std::set<std::string>& bound) const {
    for (auto& binding : bindings) {
        if (binding.fallback.has_value()) {
            auto sub_free = binding.fallback.value()->free_identifiers();
            for (auto& n : sub_free) {
                if (bound.find(n) == bound.end())
                    free.insert(n);
            }
        }
        binding.binding->free_and_bound(free, bound);
    }

    if (slurp_target.has_value())
        bound.insert(slurp_target.value());
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
                ) : opt<ExprPtr>()
        });
    return retval;
}


void MapBinding::free_and_bound(std::set<std::string>& free, std::set<std::string>& bound) const {
    for (auto& entry : entries) {
        if (entry.fallback.has_value()) {
            auto sub_free = entry.fallback.value()->free_identifiers();
            for (auto& n : sub_free) {
                if (bound.find(n) == bound.end())
                    free.insert(n);
            }
        }
        entry.binding->free_and_bound(free, bound);
    }

    if (slurp_target.has_value())
        bound.insert(slurp_target.value());
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


std::string Gold::Expr::dump() const {
    std::stringstream ss;
    ss << *this;
    return ss.str();
}


std::set<std::string> Expr::free_identifiers() const {
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


std::set<std::string> CollectionElement::free_identifiers() const {
    std::set<std::string> idents;
    free_identifiers(idents);
    return idents;
}


void SplatElement::fill(EvaluationContext& ctx, Object::ListT& list) const {
    auto val = node->evaluate(ctx);
    if (val.type() != Object::Type::list)
        throw EvalException(node->source(), fmt::format("unable to splat non-list: `{}`", val.type_name()));
    auto& inlist = val.unsafe_list();
    std::copy(inlist->begin(), inlist->end(), std::back_inserter(list));
}


void SplatElement::fill(EvaluationContext& ctx, Object::MapT& map) const {
    auto val = node->evaluate(ctx);
    if (val.type() != Object::Type::map)
        throw EvalException(node->source(), fmt::format("unable to splat non-map: `{}`", val.type_name()));
    for (auto& [key, val] : *val.unsafe_map())
        map[key] = val;
}


void SplatElement::fill(EvaluationContext& ctx, Object::ListT& list, Object::MapT& map) const {
    auto val = node->evaluate(ctx);
    if (val.type() == Object::Type::map)
        for (auto& [key, val] : *val.unsafe_map())
            map[key] = val;
    else if (val.type() == Object::Type::list) {
        auto& inlist = val.unsafe_list();
        std::copy(inlist->begin(), inlist->end(), std::back_inserter(list));
    }
    else
        throw EvalException(node->source(), fmt::format("unable to splat `{}`", val.type_name()));
}


void SplatElement::free_identifiers(std::set<std::string>& idents) const {
    node->free_identifiers(idents);
}


void SplatElement::dump(std::ostream& os) const {
    os << "Splat(" << *node << ")";
}


void CondCollectionElement::fill(EvaluationContext& ctx, Object::ListT& list) const {
    Object::MapT map;
    fill(ctx, list, map);
}


void CondCollectionElement::fill(EvaluationContext& ctx, Object::MapT& map) const {
    Object::ListT list;
    fill(ctx, list, map);
}


void CondCollectionElement::fill(EvaluationContext& ctx, Object::ListT& list, Object::MapT& map) const {
    auto c = cond->evaluate(ctx);
    if (c.type() != Object::Type::boolean)
        throw EvalException(
            cond->source(),
            fmt::format("attempted branching with non-boolean type `{}`", c.type_name())
        );
    if (c.unsafe_boolean())
        element->fill(ctx, list, map);
}


void CondCollectionElement::free_identifiers(std::set<std::string>& idents) const {
    cond->free_identifiers(idents);
    element->free_identifiers(idents);
}


void CondCollectionElement::dump(std::ostream& os) const {
    os << "Cond(" << *cond << ", " << *element << ")";
}


void LoopCollectionElement::fill(EvaluationContext& ctx, Object::ListT& list) const {
    Object::MapT map;
    fill(ctx, list, map);
}


void LoopCollectionElement::fill(EvaluationContext& ctx, Object::MapT& map) const {
    Object::ListT list;
    fill(ctx, list, map);
}


void LoopCollectionElement::fill(EvaluationContext& ctx, Object::ListT& list, Object::MapT& map) const {
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
        element->fill(ctx, list, map);
    }
    ctx.pop_namespace();
}


void LoopCollectionElement::free_identifiers(std::set<std::string>& idents) const {
    iter->free_identifiers(idents);

    std::set<std::string> bound;
    binding->free_and_bound(idents, bound);

    auto candidates = element->free_identifiers();
    for (auto& p : bound)
        candidates.erase(p);
    for (auto& c : candidates)
        idents.insert(c);
}


void LoopCollectionElement::dump(std::ostream& os) const {
    os << "For(" << *binding << ", " << *iter << ", " << *element << ")";
}


void ListElement::fill(EvaluationContext& ctx, Object::MapT& map) const {
    throw EvalException("attempted to use list element in map context");
}


void ListElement::fill(EvaluationContext& ctx, Object::ListT& list, Object::MapT& map) const {
    fill(ctx, list);
}


void MapElement::fill(EvaluationContext& ctx, Object::ListT& list) const {
    throw EvalException("attempted to use map element in list context");
}


void MapElement::fill(EvaluationContext& ctx, Object::ListT& list, Object::MapT& map) const {
    fill(ctx, map);
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


void SingletonMapElement::fill(EvaluationContext& ctx, Object::MapT& map) const {
    auto k = key->evaluate(ctx);
    if (k.type() != Object::Type::string)
        throw EvalException(
            key->source(),
            fmt::format("attempted using non-string type `{}` as object key", k.type_name())
        );
    map[k.unsafe_string()] = node->evaluate(ctx);
}


void SingletonMapElement::free_identifiers(std::set<std::string>& idents) const {
    key->free_identifiers(idents);
    node->free_identifiers(idents);
}


void SingletonMapElement::dump(std::ostream& os) const {
    os << "Entry(" << *key << ", " << *node << ")";
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
    Object::MapT map;
    for (auto& element : elements)
        element->fill(ctx, map);
    return Object::map(map);
}


void BinOp::dump(std::ostream& os) const {
    os << "BinOp(" << *lhs << " " << binop_to_string(op) << " " <<  *rhs << ")";
}


void BinOp::free_identifiers(std::set<std::string>& idents) const {
    lhs->free_identifiers(idents);
    rhs->free_identifiers(idents);
}


Object BinOp::evaluate(EvaluationContext& ctx) const {
    auto l = lhs->evaluate(ctx);
    try {
        if (op == BinaryOperator::conjunction)
            return (bool)l ? rhs->evaluate(ctx) : l;
        if (op == BinaryOperator::disjunction)
            return (bool)l ? l : rhs->evaluate(ctx);

        auto r = rhs->evaluate(ctx);
        switch (op) {
        case BinaryOperator::plus: return l + r; break;
        case BinaryOperator::minus: return l - r; break;
        case BinaryOperator::multiply: return l * r; break;
        case BinaryOperator::divide: return l / r; break;
        case BinaryOperator::power: return l.power(r); break;
        case BinaryOperator::integer_divide: return l.idiv(r); break;
        case BinaryOperator::less_than: return Object::boolean(l < r); break;
        case BinaryOperator::less_than_or_eq: return Object::boolean(l <= r); break;
        case BinaryOperator::greater_than: return Object::boolean(l > r); break;
        case BinaryOperator::greater_than_or_eq: return Object::boolean(l >= r); break;
        case BinaryOperator::equal: return Object::boolean(l == r); break;
        default: return Object::boolean(l != r); break;
        }
    }
    catch (EvalException& e) {
        e.tag_position(source());
        throw;
    }
}


void UnOp::dump(std::ostream& os) const {
    os << "UnOp(" << unop_to_string(op) << " " << *operand << ")";
}


void UnOp::free_identifiers(std::set<std::string>& idents) const {
    operand->free_identifiers(idents);
}


Object UnOp::evaluate(EvaluationContext& ctx) const {
    auto val = operand->evaluate(ctx);
    try {
        switch (op) {
        case UnaryOperator::negate: return -val; break;
        default: return Object::boolean(!(bool)val); break;
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
        binding->free_and_bound(idents, bound);
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
    os << "Function(" << *args << ", " << *kwargs << ", " << *expression << ")";
}


void Function::free_identifiers(std::set<std::string>& idents) const {
    auto candidates = expression->free_identifiers();

    std::set<std::string> bound;
    args->free_and_bound(idents, bound);
    kwargs->free_and_bound(idents, bound);

    for (auto& c : bound)
        candidates.erase(c);
    for (auto& c : candidates)
        idents.insert(c);
}


Object Function::evaluate(EvaluationContext& ctx) const {
    auto free = Expr::free_identifiers();
    auto closure = std::make_shared<Object::ClosureT>();

    for (auto& id : free) {
        auto val = ctx.weak_lookup(id);
        if (val.has_value())
            closure->nonlocals[id] = val.value();
    }

    closure->args = args;
    closure->kwargs = kwargs;
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
    for (auto& element : elements)
        os << ", " << *element;
    os << ")";
}


void FunCall::free_identifiers(std::set<std::string>& idents) const {
    function->free_identifiers(idents);
    for (auto& element : elements)
        element->free_identifiers(idents);
}


Object FunCall::evaluate(EvaluationContext& ctx) const {
    auto func = function->evaluate(ctx);
    Object::ListT arglist;
    Object::MapT kwarglist;
    for (auto& element : elements)
        element->fill(ctx, arglist, kwarglist);
    // for (auto& arg : args)
    //     arglist.push_back(arg->evaluate(ctx));

    // Object kwarglist;
    // if (!kwargs.empty()) {
    //     ctx.push_object();
    //     for (auto& kwarg : kwargs)
    //         ctx.assign_object(kwarg.first, kwarg.second->evaluate(ctx));
    //     kwarglist = ctx.finalize_object();
    // }
    // else
    //     kwarglist = Object::map();

    try {
        auto rval = func.call(ctx, Object::list(arglist), Object::map(kwarglist));
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
