#include <cinttypes>
#include <iostream>

#include <fmt/core.h>

#include <tao/pegtl.hpp>
#include <tao/pegtl/contrib/analyze.hpp>
#include <tao/pegtl/contrib/parse_tree.hpp>
#include <tao/pegtl/contrib/parse_tree_to_dot.hpp>
#include <tao/pegtl/contrib/trace.hpp>

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


namespace Grammar
{
    // Forward declarations
    struct expression;
    struct identifier_char;

    // Keywords (illegal identifiers in expressions)
    struct keyword: p::seq<
        p::sor<
            p::string<'i','f'>,
            p::string<'t','h','e','n'>,
            p::string<'e','l','s','e'>,
            p::string<'e','l','s','e'>,
            p::string<'t','r','u','e'>,
            p::string<'f','a','l','s','e'>,
            p::string<'n','u','l','l'>,
            p::string<'a','n','d'>
        >,
        p::not_at<identifier_char>
    > {};

    // Identifiers
    struct identifier_char: p::alnum {};
    struct identifier: p::seq<
        p::not_at<keyword>,
        p::plus<identifier_char>
    > {};

    // Miscellaneous
    struct whitespace: p::one<' ', '\t', '\n', '\r'> {};

    // Numbers
    struct sign: p::one<'-','+'> {};
    struct dot: p::one<'.'> {};
    struct leading: p::sor<p::one<'0'>, p::seq<p::range<'1','9'>, p::star<p::digit>>> {};
    struct trailing: p::plus<p::digit> {};
    struct exponent: p::seq<p::one<'e','E'>, p::opt<sign>, leading> {};
    struct integer: p::seq<p::opt<sign>, leading> {};
    struct float1: p::seq<p::opt<sign>, leading, dot, p::opt<trailing>, p::opt<exponent>> {};
    struct float2: p::seq<p::opt<sign>, p::opt<leading>, dot, trailing, p::opt<exponent>> {};
    struct float3: p::seq<p::opt<sign>, leading, exponent> {};
    struct floating: p::sor<float1, float2, float3> {};
    struct number: p::sor<floating, integer> {};

    // Strings
    struct escaped_unicode: p::seq<p::one<'u'>, p::rep<4, p::xdigit>> {};
    struct escaped_char: p::sor<
        p::one<'\\', '"', 'b', 'f', 'n', 'r', 't', '$'>,
        escaped_unicode
    > {};
    struct escaped: p::sor<escaped_char> {};
    struct unescaped: p::utf8::range<0x20, 0x10ffff> {};
    struct string_character: p::if_then_else<p::one<'\\'>, escaped, unescaped> {};
    struct string_data: p::seq<
        string_character,
        p::until<
            p::at<p::sor<p::eof, p::string<'$','{'>>>,
            string_character
        >
    > {};
    struct string_interp: p::seq<p::pad<expression, whitespace>, p::one<'}'>> {};
    struct string: p::until<p::at<p::one<'"'>>, string_character> {};
    struct istring: p::until<p::eof, p::if_then_else<p::string<'$','{'>, string_interp, string_data>> {};
    struct quoted_string: p::seq<p::one<'"'>, p::rematch<string, p::seq<istring, p::eof>>, p::one<'"'>> {};

    // Null
    struct nullp: p::string<'n','u','l','l'> {};

    // Booleans
    struct boolean: p::sor<p::string<'t','r','u','e'>, p::string<'f','a','l','s','e'>> {};

    // Lists
    struct splatted_atomic;
    struct list_element: p::sor<splatted_atomic, expression> {};
    struct list: p::opt<p::seq<
        p::star<whitespace>,
        p::list<list_element, p::one<','>, whitespace>,
        p::opt<p::pad<p::one<','>, whitespace>>
    >> {};
    struct bracketed_list: p::seq<p::one<'['>, list, p::pad<p::one<']'>, whitespace>> {};

    // Maps
    struct map_identifier: p::plus<p::alnum> {};
    struct map_entry: p::seq<
        map_identifier,
        p::pad<p::one<':'>, whitespace>,
        expression
    > {};
    struct map_element: p::sor<splatted_atomic, map_entry> {};
    struct map: p::opt<p::seq<
        p::star<whitespace>,
        p::list<map_element, p::one<','>, whitespace>,
        p::opt<p::pad<p::one<','>, whitespace>>
    >> {};
    struct bracketed_map: p::seq<p::one<'{'>, map, p::pad<p::one<'}'>, whitespace>> {};

    // Blocks
    struct let_identifier: p::seq<identifier> {};
    struct binding: p::seq<
        p::string<'l','e','t'>,
        p::pad<let_identifier, whitespace>,
        p::pad<p::one<'='>, whitespace>,
        expression
    > {};
    struct block: p::seq<
        p::star<whitespace>,
        p::star<p::seq<binding, p::star<whitespace>>>,
        expression
    > {};
    struct bracketed_block: p::seq<p::one<'{'>, block, p::pad<p::one<'}'>, whitespace>> {};

    // Functions
    struct param_identifier: p::seq<let_identifier> {};
    struct param_list: p::opt<p::seq<
        p::star<whitespace>,
        p::list<param_identifier, p::one<','>, whitespace>,
        p::opt<p::pad<p::one<','>, whitespace>>
    >> {};
    struct bracketed_param_list: p::seq<p::one<'('>, param_list, p::pad<p::one<')'>, whitespace>> {};
    struct function: p::seq<
        bracketed_param_list,
        p::pad<p::string<'=','>'>, whitespace>,
        p::pad<expression, whitespace>
    > {};

    // Conditionals
    struct branch: p::seq<
        p::pad<p::string<'i','f'>, whitespace>,
        p::pad<expression, whitespace>,
        p::pad<p::string<'t','h','e','n'>, whitespace>,
        p::pad<expression, whitespace>,
        p::pad<p::string<'e','l','s','e'>, whitespace>,
        p::pad<expression, whitespace>
    > {};

    // Parenthesised expressions
    struct paren: p::seq<
        p::one<'('>,
        p::pad<expression, whitespace>,
        p::one<')'>,
        p::not_at<p::pad<p::string<'=','>'>, whitespace>>
    > {};

    // Atomic expressions (can have postfix operators)
    struct pure_atomic: p::sor<
        quoted_string,
        number,
        bracketed_list,
        bracketed_map,
        bracketed_block,
        identifier,
        boolean,
        nullp,
        paren
    > {};

    // Precedence level: postfix operators
    struct funcall_args: p::opt<p::seq<
        p::star<whitespace>,
        p::list<expression, p::one<','>, whitespace>,
        p::opt<p::pad<p::one<','>, whitespace>>
    >> {};
    struct funcall_operator: p::seq<p::one<'('>, funcall_args, p::pad<p::one<')'>, whitespace>> {};
    struct object_access: p::seq<p::one<'.'>, let_identifier> {};
    struct subscript_operator: p::seq<p::one<'['>, p::pad<expression, whitespace>, p::pad<p::one<']'>, whitespace>> {};

    struct postfix: p::sor<
        funcall_operator,
        object_access,
        subscript_operator
    > {};
    struct atomic: p::seq<pure_atomic, p::star<p::pad<postfix, whitespace>>> {};

    struct splat: p::string<'.','.','.'> {};
    struct splatted_atomic: p::seq<atomic, p::pad<splat, whitespace>> {};

    // Composite expressions (can't have postfix operators)
    struct composite: p::sor<
        atomic,
        function,
        branch
    > {};

    // Binary operator template
    template <typename T, typename O>
    struct binop {
        struct operand: p::seq<T> {};
        struct optor: O {};
        struct operation: p::seq<
            operand,
            p::opt<p::seq<p::pad<optor, whitespace>, p::pad<operation, whitespace>>>
        > {};
    };

    // Binary operator precedence levels (left-to-right)
    struct product: binop<atomic, p::sor<p::string<'/','/'>, p::one<'*'>, p::one<'/'>>> {};
    struct sum: binop<product::operation, p::sor<p::string<'+'>, p::string<'-'>>> {};
    struct ineq: binop<sum::operation, p::sor<p::string<'<','='>, p::string<'>','='>, p::one<'<'>, p::one<'>'>>> {};
    struct eq: binop<ineq::operation, p::sor<p::string<'=','='>, p::string<'!','='>>> {};
    struct conj: binop<eq::operation, p::string<'a','n','d'>> {};
    struct disj: binop<conj::operation, p::string<'o','r'>> {};

    // Finalize
    struct expression: p::seq<p::sor<eq::operation, composite>> {};
    struct file: p::seq<p::bof, block, p::pad<p::eof, whitespace>> {};

    template<typename Rule>
    using selector = p::parse_tree::selector<Rule,
        p::parse_tree::store_content::on<
            number,
            integer,
            floating,
            istring,
            string_data,
            string_interp,
            nullp,
            boolean,
            list,
            splatted_atomic,
            map_identifier,
            map_entry,
            block,
            binding,
            identifier,
            let_identifier,
            param_identifier,
            param_list,
            function,
            branch,
            map,
            product::operation,
            product::optor,
            sum::operation,
            sum::optor,
            ineq::operation,
            ineq::optor,
            eq::operation,
            eq::optor,
            conj::operation,
            conj::optor,
            disj::operation,
            disj::optor,
            atomic,
            funcall_operator,
            object_access,
            subscript_operator,
            file
        >
    >;
}


static Source source(p::parse_tree::node& node) {
    auto src = node.begin();
    return Source { src.byte, src.line, src.column };
}


static std::string codepoint_as_string(const char* it, int nchars) {
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

    std::cout << codepoint << std::endl;

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


static std::unique_ptr<AstNode> normalize(p::parse_tree::node& node) {
    if (node.is_root()) {
        if (node.children.size() != 1)
            throw ParseException();
        return normalize(*node.children[0]);
    }

    if (node.type == "Grammar::file") {
        return normalize(*node.children[0]);
    }

    else if (node.type == "Grammar::boolean") {
        Object obj = Object::boolean(node.string_view() == "true");
        return std::make_unique<Literal>(source(node), obj);
    }

    else if (node.type == "Grammar::number") {
        auto& c = node.children[0];

        if (c->type == "Grammar::integer") {
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

    else if (node.type == "Grammar::string_data") {
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

    else if (node.type == "Grammar::string_interp") {
        auto func = std::make_unique<Identifier>(source(node), "str");
        auto call = std::make_unique<FunCall>(source(node), std::move(func));
        call->append(normalize(*node.children[0]));
        return call;
    }

    else if (node.type == "Grammar::istring") {
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

    else if (node.type == "Grammar::nullp") {
        return std::make_unique<Literal>(source(node), Object::null());
    }

    else if (node.type == "Grammar::identifier") {
        return std::make_unique<Identifier>(source(node), node.string());
    }

    else if (node.type == "Grammar::list") {
        auto list = std::make_unique<List>(source(node));
        for (auto&& c : node.children) {
            if (c->type == "Grammar::splatted_atomic")
                list->append(normalize(*c->children[0]), true);
            else
                list->append(normalize(*c), false);
        }
        return list;
    }

    else if (node.type == "Grammar::map") {
        auto map = std::make_unique<Map>(source(node));
        for (auto&& c : node.children) {
            if (c->type == "Grammar::splatted_atomic") {
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

    else if (node.type.substr(0, 14) == "Grammar::binop")
    {
        if (node.children.size() == 1)
            return normalize(*node.children[0]);
        return std::make_unique<BinOp>(
            source(node),
            normalize(*node.children[0]),
            normalize(*node.children[2]),
            operator_from_string(node.children[1]->string())
        );
    }

    else if (node.type == "Grammar::block") {
        auto block = std::make_unique<Block>(source(node));
        for (auto&& c : node.children) {
            if (c->type == "Grammar::binding")
                block->append(c->children[0]->string(), normalize(*c->children[1]));
            else
                block->set_expression(normalize(*c));
        }
        return block;
    }

    else if (node.type == "Grammar::function") {
        auto function = std::make_unique<Function>(source(node));
        for (auto&& c : node.children[0]->children) {
            function->append(c->string());
        }
        function->set_expression(normalize(*node.children[1]));
        return function;
    }

    else if (node.type == "Grammar::branch")
        return std::make_unique<Branch>(
            source(node),
            normalize(*node.children[0]),
            normalize(*node.children[1]),
            normalize(*node.children[2])
        );

    else if (node.type == "Grammar::atomic") {
        auto it = node.children.begin();
        auto value = normalize(**it++);
        while (it != node.children.end()) {
            if ((*it)->type == "Grammar::funcall_operator") {
                auto funcall = std::make_unique<FunCall>(source(**it), std::move(value));
                for (auto&& c : (*it)->children)
                    funcall->append(normalize(*c));
                value = std::move(funcall);
            }
            else if ((*it)->type == "Grammar::object_access") {
                auto field = Object::string((*it)->children[0]->string());
                auto index = std::make_unique<Index>(
                    source(**it),
                    std::move(value),
                    std::make_unique<Literal>(source(**it), field)
                );
                value = std::move(index);
            }
            else if ((*it)->type == "Grammar::subscript_operator") {
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

    std::cout << node.type << std::endl;
    throw ParseException();
}


bool Gold::analyze_grammar() {
    return p::analyze<Grammar::file>() == 0;
}


void Gold::debug_parse(std::string input, bool as_expression) {
    p::string_input in(input, "x");
    if (as_expression)
        p::standard_trace<Grammar::expression>(in);
    else
        p::standard_trace<Grammar::file>(in);
}


void Gold::debug_parse_tree(std::string input, bool as_expression) {
    p::string_input in(input, "x");
    auto tree = as_expression ?
        p::parse_tree::parse<Grammar::expression, Grammar::selector>(in) :
        p::parse_tree::parse<Grammar::file, Grammar::selector>(in);
    p::parse_tree::print_dot(std::cout, *tree);
}


template <typename I>
static std::unique_ptr<AstNode> _parse(I& input, bool as_expression) {
    try {
        auto tree = as_expression ?
            p::parse_tree::parse<Grammar::expression, Grammar::selector>(input) :
            p::parse_tree::parse<Grammar::file, Grammar::selector>(input);
        if (!tree)
            throw ParseException();
        return normalize(*tree);
    }
    catch (const p::parse_error& e) {
        throw ParseException();
    }
}


std::unique_ptr<AstNode> Gold::parse_string(std::string code, bool as_expression) {
    p::string_input in(code, "code");
    return _parse(in, as_expression);
}


std::unique_ptr<AstNode> Gold::parse_file(std::string path, bool as_expression) {
    p::file_input in(path, "code");
    return _parse(in, as_expression);
}


Object Gold::evaluate_string(std::string code) {
    EvaluationContext ctx;
    return evaluate_string(ctx, code);
}


Object Gold::evaluate_string(EvaluationContext& ctx, std::string code) {
    auto ast = parse_string(code, false);
    auto value = ast->evaluate(ctx);
    return value;
}


Object Gold::evaluate_file(std::string code) {
    EvaluationContext ctx;
    return evaluate_file(ctx, code);
}


Object Gold::evaluate_file(EvaluationContext& ctx, std::string path) {
    auto ast = parse_file(path, false);
    auto value = ast->evaluate(ctx);
    return value;
}
