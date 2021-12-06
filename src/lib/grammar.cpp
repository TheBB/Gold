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
using namespace Gold::Ast;
namespace p = tao::pegtl;


std::ostream& operator<<(std::ostream& os, Operator op) {
    switch (op) {
    case Operator::plus: os << "+"; break;
    case Operator::minus: os << "-"; break;
    case Operator::multiply: os << "*"; break;
    case Operator::divide: os << "/"; break;
    case Operator::integer_divide: os << "//"; break;
    }
    return os;
}


std::string Gold::Ast::Node::dump() const {
    std::stringstream ss;
    ss << *this;
    return ss.str();
}


std::ostream& operator<<(std::ostream& os, const Node& obj) {
    obj.dump(os);
    return os;
}


void Gold::Ast::List::dump(std::ostream& os) const {
    os << "List(";
    bool first = true;
    for (auto& obj : elements) {
        if (!first)
            os << ", ";
        os << *obj;
        first = false;
    }
    os << ")";
}


void Gold::Ast::Map::dump(std::ostream& os) const {
    os << "Map(";
    bool first = true;
    for (auto& [key, value] : entries) {
        if (!first)
            os << ", ";
        os << "Entry(" << key << ", " << *value << ")";
        first = false;
    }
    os << ")";
}


void Gold::Ast::OpSeq::dump(std::ostream& os) const {
    os << "OpSeq(" << *initial;
    for (auto& [op, value] : sequence)
        os << " " << op << " " << *value;
    os << ")";
}


void Gold::Ast::Block::dump(std::ostream& os) const {
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


void Gold::Ast::Function::dump(std::ostream& os) const {
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


void Gold::Ast::Branch::dump(std::ostream& os) const {
    os << "Branch(" << *condition << ", " << *if_value << ", " << *else_value << ")";
}


void Gold::Ast::FunCall::dump(std::ostream& os) const {
    os << "FunCall(" << *function;
    for (auto& arg : args)
        os << ", " << *arg;
    os << ")";
}


void Gold::Ast::Index::dump(std::ostream& os) const {
    os << "Index(" << *haystack << ", " << *needle << ")";
}


static Operator operator_from_string(std::string value) {
    if (value == "+") return Operator::plus;
    if (value == "-") return Operator::minus;
    if (value == "*") return Operator::multiply;
    if (value == "/") return Operator::divide;
    return Operator::integer_divide;
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
            p::string<'e','l','s','e'>
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
    struct integer: p::sor<p::one<'0'>, p::seq<p::range<'1','9'>, p::star<p::digit>>> {};
    struct fractional: p::seq<p::one<'.'>, p::star<p::digit>> {};
    struct exponent: p::seq<p::one<'e','E'>, p::opt<sign>, integer> {};
    struct number: p::seq<p::opt<sign>, integer, p::opt<fractional>, p::opt<exponent>> {};

    // Strings
    // struct escaped_unicode: p::seq<p::one<'u'>, p::rep<4, p::xdigit>> {};
    struct escaped_char: p::one<'\\', '"'> {};
    struct escaped: p::sor<escaped_char> {};
    struct unescaped: p::utf8::range<0x20, 0x10ffff> {};
    struct character: p::if_then_else<p::one<'\\'>, escaped, unescaped> {};
    struct string: p::until<p::at<p::one<'"'>>, character> {};
    struct quoted_string: p::seq<p::one<'"'>, string, p::one<'"'>> {};

    // Booleans
    struct boolean: p::sor<p::string<'t','r','u','e'>, p::string<'f','a','l','s','e'>> {};

    // Lists
    struct list: p::opt<p::seq<
        p::star<whitespace>,
        p::list<expression, p::one<','>, whitespace>,
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
    struct map: p::opt<p::seq<
        p::star<whitespace>,
        p::list<map_entry, p::one<','>, whitespace>,
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
        boolean,
        bracketed_list,
        bracketed_map,
        bracketed_block,
        identifier,
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

    // Composite expressions (can't have postfix operators)
    struct composite: p::sor<
        atomic,
        function,
        branch
    > {};

    // Precedence level: multiplication
    struct factor: p::seq<atomic> {};
    struct product_operator: p::sor<p::string<'/','/'>, p::one<'*'>, p::one<'/'>> {};
    struct product: p::list<factor, product_operator, whitespace> {};

    // Precedence level: addition
    struct term: p::seq<product> {};
    struct sum_operator: p::sor<p::one<'+'>, p::one<'-'>> {};
    struct sum: p::list<term, sum_operator, whitespace> {};

    struct expression: p::seq<p::sor<sum, composite>> {};
    struct file: p::seq<p::bof, block, p::pad<p::eof, whitespace>> {};

    template<typename Rule>
    using selector = p::parse_tree::selector<Rule,
        p::parse_tree::store_content::on<
            number,
            sign,
            integer,
            fractional,
            exponent,
            string,
            boolean,
            list,
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
            sum,
            sum_operator,
            product,
            product_operator,
            atomic,
            funcall_operator,
            object_access,
            subscript_operator,
            file
        >
    >;
}


static std::unique_ptr<Node> normalize(p::parse_tree::node& node) {
    if (node.is_root()) {
        if (node.children.size() != 1)
            throw ParseException();
        return normalize(*node.children[0]);
    }

    if (node.type == "Grammar::file") {
        auto function = std::make_unique<Function>();
        function->set_expression(normalize(*node.children[0]));
        return std::make_unique<FunCall>(std::move(function));
    }

    else if (node.type == "Grammar::boolean") {
        Object obj = Object::boolean(node.string_view() == "true");
        return std::make_unique<Literal>(obj);
    }

    else if (node.type == "Grammar::number") {
        bool positive = true;
        intmax_t integer = 0;

        for (auto&& c : node.children) {
            if (c->type == "Grammar::sign") {
                positive = c->string_view() == "+";
            }
            else if (c->type == "Grammar::integer") {
                for (auto ch : c->string_view()) {
                    integer *= 10;
                    integer += ch - '0';
                }
            }
            else if (c->type == "Grammar::fractional" || c->type == "Grammar::exponent") {
                double value = std::stod(node.string());
                Object obj = Object::floating(value);
                return std::make_unique<Literal>(obj);
            }
        }

        if (!positive)
            integer *= -1;

        Object obj = Object::integer(integer);
        return std::make_unique<Literal>(obj);
    }

    else if (node.type == "Grammar::string") {
        auto data = node.string_view();
        std::stringstream builder;
        for (auto it = data.begin(); it != data.end(); it++) {
            if (*it == '\\') {
                it++;
                builder << *it;
            }
            else
                builder << *it;
        }
        Object obj = Object::string(builder.str());
        return std::make_unique<Literal>(obj);
    }

    else if (node.type == "Grammar::identifier") {
        return std::make_unique<Identifier>(node.string());
    }

    else if (node.type == "Grammar::list") {
        auto list = std::make_unique<List>();
        for (auto&& c : node.children) {
            list->append(normalize(*c));
        }
        return list;
    }

    else if (node.type == "Grammar::map") {
        auto map = std::make_unique<Map>();
        for (auto&& c : node.children) {
            auto key = c->children[0]->string();
            auto value = normalize(*c->children[1]);
            map->append(key, std::move(value));
        }
        return map;
    }

    else if (node.type == "Grammar::sum" || node.type == "Grammar::product") {
        if (node.children.size() == 1)
            return normalize(*node.children[0]);
        auto it = node.children.begin();
        auto opseq = std::make_unique<OpSeq>(normalize(**it++));
        while (it != node.children.end()) {
            auto op = operator_from_string((*it++)->string());
            opseq->append(op, normalize(**it++));
        }
        return opseq;
    }

    else if (node.type == "Grammar::block") {
        auto block = std::make_unique<Block>();
        for (auto&& c : node.children) {
            if (c->type == "Grammar::binding")
                block->append(c->children[0]->string(), normalize(*c->children[1]));
            else
                block->set_expression(normalize(*c));
        }
        return block;
    }

    else if (node.type == "Grammar::function") {
        auto function = std::make_unique<Function>();
        for (auto&& c : node.children[0]->children) {
            function->append(c->string());
        }
        function->set_expression(normalize(*node.children[1]));
        return function;
    }

    else if (node.type == "Grammar::branch")
        return std::make_unique<Branch>(
            normalize(*node.children[0]),
            normalize(*node.children[1]),
            normalize(*node.children[2])
        );

    else if (node.type == "Grammar::atomic") {
        auto it = node.children.begin();
        auto value = normalize(**it++);
        while (it != node.children.end()) {
            if ((*it)->type == "Grammar::funcall_operator") {
                auto funcall = std::make_unique<FunCall>(std::move(value));
                for (auto&& c : (*it)->children)
                    funcall->append(normalize(*c));
                value = std::move(funcall);
            }
            else if ((*it)->type == "Grammar::object_access") {
                auto field = Object::string((*it)->children[0]->string());
                auto index = std::make_unique<Index>(
                    std::move(value),
                    std::make_unique<Literal>(field)
                );
                value = std::move(index);
            }
            else if ((*it)->type == "Grammar::subscript_operator") {
                auto index = std::make_unique<Index>(
                    std::move(value),
                    normalize(*(*it)->children[0])
                );
                value = std::move(index);
            }
            it++;
        }
        return value;
    }

    throw ParseException();
}


bool Gold::Ast::analyze_grammar() {
    return p::analyze<Grammar::file>() == 0;
}


void Gold::Ast::debug_parse(std::string input, bool as_expression) {
    p::string_input in(input, "x");
    if (as_expression)
        p::standard_trace<Grammar::expression>(in);
    else
        p::standard_trace<Grammar::file>(in);
}


void Gold::Ast::debug_parse_tree(std::string input, bool as_expression) {
    p::string_input in(input, "x");
    auto tree = as_expression ?
        p::parse_tree::parse<Grammar::expression, Grammar::selector>(in) :
        p::parse_tree::parse<Grammar::file, Grammar::selector>(in);
    p::parse_tree::print_dot(std::cout, *tree);
}


std::unique_ptr<Node> Gold::Ast::parse(std::string input, bool as_expression)
{
    p::string_input in(input, "x");
    try {
        auto tree = as_expression ?
            p::parse_tree::parse<Grammar::expression, Grammar::selector>(in) :
            p::parse_tree::parse<Grammar::file, Grammar::selector>(in);
        if (!tree)
            throw ParseException();
        return normalize(*tree);
    }
    catch (const p::parse_error& e) {
        throw ParseException();
    }
}
