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

    // Right-associative binary operator template
    template <typename T, typename O>
    struct rbinop {
        struct operand: p::seq<T> {};
        struct optor: O {};
        struct operation: p::seq<
            operand,
            p::opt<p::seq<p::pad<optor, whitespace>, p::pad<operation, whitespace>>>
        > {};
    };

    // Left-associative operator sequence template
    template <typename T, typename O>
    struct lbinop {
        struct operand: p::seq<T> {};
        struct optor: O {};
        struct operation: p::list<operand, optor, whitespace> {};
    };

    // Binary operator precedence levels (left-to-right)
    struct product: lbinop<atomic, p::sor<p::string<'/','/'>, p::one<'*'>, p::one<'/'>>> {};
    struct sum: lbinop<product::operation, p::sor<p::string<'+'>, p::string<'-'>>> {};
    struct ineq: lbinop<sum::operation, p::sor<p::string<'<','='>, p::string<'>','='>, p::one<'<'>, p::one<'>'>>> {};
    struct eq: lbinop<ineq::operation, p::sor<p::string<'=','='>, p::string<'!','='>>> {};
    struct conj: lbinop<eq::operation, p::string<'a','n','d'>> {};
    struct disj: lbinop<conj::operation, p::string<'o','r'>> {};

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
    catch (const p::parse_error&) {
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
