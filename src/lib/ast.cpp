#include <cinttypes>
#include <iostream>
#include <string>

#include <fmt/core.h>

#include <tao/pegtl/contrib/parse_tree.hpp>

#include "gold.hpp"
#include "parsing.hpp"

using namespace Gold;
namespace p = tao::pegtl;


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
    case Operator::disjunction: return "or";
    }
    return "?";
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


std::ostream& operator<<(std::ostream& os, Operator op) {
    os << operator_to_string(op);
    return os;
}


std::string Gold::AstNode::dump() const {
    std::stringstream ss;
    ss << *this;
    return ss.str();
}


std::ostream& operator<<(std::ostream& os, const AstNode& obj) {
    obj.dump(os);
    return os;
}


std::set<std::string> AstNode::free_identifiers() const {
    std::set<std::string> idents;
    free_identifiers(idents);
    return idents;
}


Object Identifier::evaluate(EvaluationContext& ctx) const {
    try {
        return ctx.lookup(name);
    }
    catch (EvalException& e) {
        e.position(source());
        throw;
    }
}


void List::dump(std::ostream& os) const {
    os << "List(";
    bool first = true;
    for (auto& entry : elements) {
        if (!first)
            os << ", ";
        if (entry.splat)
            os << "Splat(" << *entry.node << ")";
        else
            os << *entry.node;
        first = false;
    }
    os << ")";
}


void List::free_identifiers(std::set<std::string>& idents) const {
    for (auto& entry : elements)
        entry.node->free_identifiers(idents);
}


Object List::evaluate(EvaluationContext& ctx) const {
    std::vector<Object> objs;
    for (auto& entry : elements) {
        auto val = entry.node->evaluate(ctx);
        if (entry.splat) {
            if (val.type() != Object::Type::list)
                throw EvalException(entry.node->source(), fmt::format("unable to splat non-list: `{}`", val.type_name()));
            auto& list = val.unsafe_list();
            std::copy(list->begin(), list->end(), std::back_inserter(objs));
        }
        else
            objs.push_back(entry.node->evaluate(ctx));
    }
    return Object::list(std::move(objs));
}


void Map::dump(std::ostream& os) const {
    os << "Map(";
    bool first = true;
    for (auto& entry : entries) {
        if (!first)
            os << ", ";
        if (entry.splat)
            os << "Splat(" << *entry.node << ")";
        else
            os << "Entry(" << entry.key << ", " << *entry.node << ")";
        first = false;
    }
    os << ")";
}


void Map::free_identifiers(std::set<std::string>& idents) const {
    for (auto& obj : entries)
        obj.node->free_identifiers(idents);
}


Object Map::evaluate(EvaluationContext& ctx) const {
    ctx.push_object();
    for (auto& entry : entries) {
        auto value = entry.node->evaluate(ctx);
        if (entry.splat) {
            if (value.type() != Object::Type::map)
                throw EvalException(entry.node->source(), fmt::format("unable to splat non-map: `{}`", value.type_name()));
            auto& map = value.unsafe_map();
            for (auto& [key, val] : *map)
                ctx.assign_object(key, val);
        }
        else
            ctx.assign_object(entry.key, value);
    }
    return ctx.finalize_object();
}


void BinOp::dump(std::ostream& os) const {
    os << "BinOp(" << *lhs << " " << op << " " <<  *rhs << ")";
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
        case Operator::not_equal: return Object::boolean(l != r); break;
        default: throw InternalException();
        }
    }
    catch (EvalException& e) {
        e.position(source());
        throw;
    }

    throw InternalException();
}


void Block::dump(std::ostream& os) const {
    os << "Block(";
    bool first = true;
    for (auto& [name, value] : bindings) {
        if (!first)
            os << ", ";
        os << "Entry(" << name << ", " << *value << ")";
        first = false;
    }
    if (!first)
        os << ", ";
    os << *expression << ")";
}


void Block::free_identifiers(std::set<std::string>& idents) const {
    std::set<std::string> bound;
    for (auto& [key, val] : bindings) {
        auto candidates = val->free_identifiers();
        for (auto& c : candidates) {
            if (bound.find(c) == bound.end())
                idents.insert(c);
        }
        bound.insert(key);
    }
    auto candidates = expression->free_identifiers();
        for (auto& c : candidates) {
            if (bound.find(c) == bound.end())
                idents.insert(c);
        }
}


Object Block::evaluate(EvaluationContext& ctx) const {
    ctx.push_namespace();
    for (auto& [key, value] : bindings) {
        ctx.assign(key, value->evaluate(ctx));
    }
    auto retval = expression->evaluate(ctx);
    ctx.pop_namespace();
    return retval;
}


void Function::dump(std::ostream& os) const {
    os << "Function(";
    bool first = true;
    for (auto& p : parameters) {
        if (!first)
            os << ", ";
        os << p;
        first = false;
    }
    if (!first)
        os << ", ";
    os << *expression << ")";
}


void Function::free_identifiers(std::set<std::string>& idents) const {
    auto candidates = expression->free_identifiers();
    for (auto& p : parameters)
        candidates.erase(p);
    for (auto& c : candidates)
        idents.insert(c);
}


Object Function::evaluate(EvaluationContext& ctx) const {
    auto free = AstNode::free_identifiers();
    auto closure = std::make_shared<Object::ClosureT>();

    try {
        for (auto& id : free)
            closure->nonlocals[id] = ctx.lookup(id);
    }
    catch (EvalException& e) {
        e.position(source());
        throw;
    }

    closure->parameters = parameters;
    closure->expression = AstNode::deserialize(expression->serialize());
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
        return func(ctx, arglist);
    }
    catch (EvalException& e) {
        e.position(source());
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
        e.position(source());
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
    else {
        char a = ((codepoint & 0b1111'0000'0000'0000) >> 12) | 0b1110'0000;
        char b = ((codepoint & 0b0000'1111'1100'0000) >>  6) | 0b1000'0000;
        char c = ((codepoint & 0b0000'0000'0011'1111) >>  0) | 0b1000'0000;
        return std::string{a,b,c};
    }

    return "";
}


static std::string nodetype(p::parse_tree::node& node) {
    std::string type(node.type);
    if (type.substr(0, 6) == "struct")
        type = type.substr(7);
    return type;
}


AstPtr Gold::normalize(p::parse_tree::node& node) {
    if (node.is_root()) {
        if (node.children.size() != 1)
            throw ParseException();
        return normalize(*node.children[0]);
    }

    auto type = nodetype(node);

    if (type == "Grammar::file") {
        return normalize(*node.children[0]);
    }

    else if (type == "Grammar::boolean") {
        Object obj = Object::boolean(node.string_view() == "true");
        return std::make_unique<Literal>(source(node), obj);
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
        call->append(normalize(*node.children[0]));
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

    else if (type == "Grammar::list::seq") {
        auto list = std::make_unique<List>(source(node));
        for (auto&& c : node.children) {
            if (nodetype(*c) == "Grammar::splatted")
                list->append(normalize(*c->children[0]), true);
            else
                list->append(normalize(*c), false);
        }
        return list;
    }

    else if (type == "Grammar::map::seq") {
        auto map = std::make_unique<Map>(source(node));
        for (auto&& c : node.children) {
            if (nodetype(*c) == "Grammar::splatted") {
                auto value = normalize(*c->children[0]);
                map->append("", std::move(value), true);
            }
            else {
                auto key = c->children[0]->string();
                auto value = normalize(*c->children[1]);
                map->append(key, std::move(value), false);
            }
        }
        return map;
    }

    else if (type.substr(0, 15) == "Grammar::rbinop") {
        if (node.children.size() == 1)
            return normalize(*node.children[0]);
        return std::make_unique<BinOp>(
            source(node),
            normalize(*node.children[0]),
            normalize(*node.children[2]),
            operator_from_string(node.children[1]->string())
        );
    }

    else if (type.substr(0, 15) == "Grammar::lbinop") {
        auto it = node.children.begin();
        auto ast = normalize(**it++);
        while (it != node.children.end()) {
            auto op = operator_from_string((*it++)->string());
            ast = std::make_unique<BinOp>(
                source(node),
                std::move(ast),
                normalize(**it++),
                op
            );
        }
        return ast;
    }

    else if (type == "Grammar::block::rule") {
        if (node.children.size() == 1)
            return normalize(*node.children[0]);
        auto block = std::make_unique<Block>(source(node));
        for (auto&& c : node.children) {
            if (nodetype(*c) == "Grammar::block::binding")
                block->append(c->children[0]->string(), normalize(*c->children[1]));
            else
                block->set_expression(normalize(*c));
        }
        return block;
    }

    else if (type == "Grammar::func::rule") {
        auto function = std::make_unique<Function>(source(node));
        for (auto&& c : node.children[0]->children) {
            function->append(c->string());
        }
        function->set_expression(normalize(*node.children[1]));
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
                    funcall->append(normalize(*c));
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

    std::cerr << type << std::endl;
    throw ParseException();
}
