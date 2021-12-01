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


std::ostream& operator<<(std::ostream& os, const AstNode& obj) {
    obj.dump(os);
    return os;
}


void LiteralNode::dump(std::ostream& os) const {
    os << _obj;
}


namespace Grammar
{
    // Forward declarations
    struct atomic;

    // Miscellaneous
    struct whitespace: p::one<' ', '\t', '\n', '\r'> {};

    // Numbers
    struct sign: p::one<'-','+'> {};
    struct integer: p::seq<p::range<'1','9'>, p::star<p::digit>> {};
    struct fractional: p::seq<p::star<p::digit>> {};
    struct exponent: p::seq<p::one<'e','E'>, p::opt<sign>, integer> {};
    struct number: p::seq<p::opt<sign>, integer, p::opt<p::seq<p::one<'.'>, fractional>>, p::opt<exponent>> {};

    // Strings
    struct escaped_unicode: p::seq<p::one<'u'>, p::rep<4, p::xdigit>> {};
    struct escaped_char: p::one<'\\', '"'> {};
    struct escaped: p::sor<escaped_char, escaped_unicode> {};
    struct unescaped: p::utf8::range<0x20, 0x10ffff> {};
    struct character: p::if_then_else<p::one<'\\'>, escaped, unescaped> {};
    struct string: p::until<p::at<p::one<'"'>>, character> {};
    struct quoted_string: p::seq<p::one<'"'>, string> {};

    // Booleans
    struct boolean: p::sor<p::string<'t','r','u','e'>, p::string<'f','a','l','s','e'>> {};

    // Lists
    struct list: p::opt<p::seq<
        p::star<whitespace>,
        p::list<atomic, p::one<','>, whitespace>,
        p::opt<p::pad<p::one<','>, whitespace>>
    >> {};
    struct bracketed_list: p::seq<p::one<'['>, list, p::pad<p::one<']'>, whitespace>> {};

    // Operator chain
    struct atomic: p::sor<quoted_string, number, boolean, bracketed_list> {};

    struct grammar: p::seq<atomic> {};

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
            list
        >>;
}


static std::unique_ptr<AstNode> normalize(std::unique_ptr<p::parse_tree::node> node) {
    if (node->is_root()) {
        if (node->children.size() != 1)
            return nullptr;
        return normalize(std::move(node->children[0]));
    }

    if (node->type == "Grammar::boolean") {
        bool value = node->string_view() == "true";
        return std::unique_ptr<AstNode>((AstNode*) new LiteralNode(Object::boolean(value)));
    }

    return nullptr;
}


bool Gold::analyze_grammar() {
    return p::analyze<Grammar::grammar>() == 0;
}


void Gold::debug_parse(std::string& input) {
    p::string_input in(input, "x");
    p::standard_trace<Grammar::grammar>(in);
}


std::unique_ptr<AstNode> Gold::parse(std::string input)
{
    p::string_input nin(input, "x");
    auto tree = p::parse_tree::parse<Grammar::grammar, Grammar::selector>(nin);
    if (!tree)
        return nullptr;
    return normalize(std::move(tree));
}
