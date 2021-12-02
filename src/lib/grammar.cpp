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


std::ostream& operator<<(std::ostream& os, const AstNode& obj) {
    obj.dump(os);
    return os;
}


void AstNode::dump(std::ostream& os) const {
    switch (type()) {
    case Type::literal:
        os << unsafe_object();
        break;
    case Type::list: {
        os << "List(" << std::endl;
        bool first = true;
        for (auto& obj : unsafe_list()) {
            if (!first)
                os << ", ";
            os << obj;
            first = false;
        }
        os << ")";
        break;
    }
    case Type::map: {
        os << "Map(";
        bool first = true;
        for (auto& [key, value] : unsafe_map()) {
            if (!first)
                os << ", ";
            os << "Entry(" << key << ", " << value << ")";
            first = false;
        }
        os << ")";
        break;
    }
    case Type::opseq: {
        os << "Opseq(";
        auto opseq = unsafe_opseq();
        auto operand_it = opseq.operands.begin();
        auto operator_it = opseq.operators.begin();
        os << *operand_it++;
        while (operand_it != opseq.operands.end())
            os << " " << *operator_it++ << " " << *operand_it++;
        os << ")";
        break;
    }
    }
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

    // Atomic expressions
    struct atomic: p::sor<
        quoted_string,
        number,
        boolean,
        bracketed_list,
        bracketed_map
    > {};

    // Precedence level: multiplication
    struct factor: p::seq<atomic> {};
    struct product_operator: p::sor<p::string<'/','/'>, p::one<'*'>, p::one<'/'>> {};
    struct product: p::list<factor, product_operator, whitespace> {};

    // Precedence level: addition
    struct term: p::seq<product> {};
    struct sum_operator: p::sor<p::one<'+'>, p::one<'-'>> {};
    struct sum: p::list<term, sum_operator, whitespace> {};

    struct expression: p::seq<sum> {};
    struct grammar: p::seq<expression> {};

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
            map,
            sum,
            sum_operator,
            product,
            product_operator
        >>;
}


static AstNode normalize(std::unique_ptr<p::parse_tree::node> node) {
    if (node->is_root()) {
        if (node->children.size() != 1)
            throw ParseException();
        return normalize(std::move(node->children[0]));
    }

    if (node->type == "Grammar::boolean") {
        Object obj = Object::boolean(node->string_view() == "true");
        return AstNode(obj);
    }

    else if (node->type == "Grammar::number") {
        bool positive = true;
        intmax_t integer = 0;

        for (auto&& c : node->children) {
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
                double value = std::stod(node->string());
                Object obj = Object::floating(value);
                return AstNode(obj);
            }
        }

        if (!positive)
            integer *= -1;

        Object obj = Object::integer(integer);
        return AstNode(obj);
    }

    else if (node->type == "Grammar::string") {
        auto data = node->string_view();
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
        return AstNode(obj);
    }

    else if (node->type == "Grammar::list") {
        AstNode::List elements;
        for (auto&& c : node->children) {
            elements.push_back(normalize(std::move(c)));
        }
        return AstNode(elements);
    }

    else if (node->type == "Grammar::map") {
        AstNode::Map entries;
        for (auto&& c : node->children) {
            auto key = c->children[0]->string();
            auto value = normalize(std::move(c->children[1]));
            entries.push_back(std::pair(key, value));
        }
        return AstNode(entries);
    }

    else if (node->type == "Grammar::sum" || node->type == "Grammar::product") {
        if (node->children.size() == 1)
            return normalize(std::move(node->children[0]));
        AstNode::Operator seq;
        auto it = node->children.begin();
        seq.operands.push_back(normalize(std::move(*it++)));
        while (it != node->children.end()) {
            seq.operators.push_back(operator_from_string((*it++)->string()));
            seq.operands.push_back(normalize(std::move(*it++)));
        }
        return AstNode(seq);
    }

    throw ParseException();
}


bool Gold::analyze_grammar() {
    return p::analyze<Grammar::grammar>() == 0;
}


void Gold::debug_parse(std::string input) {
    p::string_input in(input, "x");
    p::standard_trace<Grammar::grammar>(in);
}


void Gold::debug_parse_tree(std::string input) {
    p::string_input in(input, "x");
    auto tree = p::parse_tree::parse<Grammar::grammar, Grammar::selector>(in);
    p::parse_tree::print_dot(std::cout, *tree);
}


AstNode Gold::parse(std::string input)
{
    p::string_input in(input, "x");
    try {
        auto tree = p::parse_tree::parse<Grammar::grammar, Grammar::selector>(in);
        if (!tree)
            throw ParseException();
        return normalize(std::move(tree));
    }
    catch (const p::parse_error& e) {
        throw ParseException();
    }
}
