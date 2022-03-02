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
    /*

    Generally, rules are responsible for consuming whitespace before and should
    not consume whitespace after.  For this, we use the prepad template below.

    Atomic expressions are strings, numbers, lists, maps, identifiers, the true,
    false and null constants as well as parenthesised expressions.

    All atomic expressions may be followed by postfix operators: object access,
    subscripting and function calls.

    Postfixed expressions in turn, constitute the building blocks for the
    operator hierarchy, from highest to lowest precedence.

    Operator expressions, together with function definitions, branches and
    let-expressions constitute the wider class of composite expressions.  The
    non-postfixed expressions may not participate in operator expressions unless
    parenthesised.

    */

    // Forward declarations
    struct expression;
    struct splatted;
    struct identifier_char: p::sor<
        p::alnum,
        p::one<'_'>
    > {};

    // Ignorables: whitespace and comments
    struct ignore {
        struct whitespace_noeol: p::one<' ', '\t', '\n', '\r'> {};
        struct whitespace: p::sor<whitespace_noeol, p::one<'\n'>> {};
        struct comment: p::seq<p::one<'#'>, p::until<p::eolf>> {};
        struct noeol: p::sor<whitespace_noeol, comment> {};
        struct rule: p::sor<whitespace, comment> {};
    };

    // Keywords - these rules do not consume leading whitespace
    struct keyword {
        struct For: p::string<'f','o','r'> {};
        struct If: p::string<'i','f'> {};
        struct Then: p::string<'t','h','e','n'> {};
        struct Else: p::string<'e','l','s','e'> {};
        struct Let: p::string<'l','e','t'> {};
        struct In: p::string<'i','n'> {};
        struct True: p::string<'t','r','u','e'> {};
        struct False: p::string<'f','a','l','s','e'> {};
        struct Null: p::string<'n','u','l','l'> {};
        struct And: p::string<'a','n','d'> {};
        struct Or: p::string<'o','r'> {};

        struct any: p::sor<If, Then, Else, Let, In, True, False, Null, And, Or> {};
        struct rule: p::seq<any, p::not_at<identifier_char>> {};
    };

    // Prepad: consume whitespace before a rule but not after
    template <typename T, typename W = ignore::rule>
    struct prepad: p::pad<T, W, p::failure> {};

    // Common tokens
    struct token {
        struct equals: prepad<p::one<'='>> {};
        struct colon: prepad<p::one<':'>> {};
        struct dot: prepad<p::one<'.'>> {};
        struct comma: prepad<p::one<','>> {};
        struct op_paren: prepad<p::one<'('>> {};
        struct cl_paren: prepad<p::one<')'>> {};
        struct op_brace: prepad<p::one<'{'>> {};
        struct cl_brace: prepad<p::one<'}'>> {};
        struct op_bracket: prepad<p::one<'['>> {};
        struct cl_bracket: prepad<p::one<']'>> {};
        struct dollar: prepad<p::one<'$'>> {};
        struct implies: prepad<p::string<'=','>'>> {};
        struct splat: prepad<p::string<'.','.','.'>> {};
    };

    // List of elements separated by commas with optional trailing comma
    // This rule does not consume surrounding delimiters
    template <typename T>
    struct listof: p::opt<p::seq<p::list<T, token::comma>, p::opt<token::comma>>> {};

    // List of elements separated by commas with optional terminating element and trailing comma
    // This rule does not consume surrounding delimiters
    template <typename T, typename X>
    struct listof_term: p::opt<
        p::seq<p::list<T, token::comma>>,
        p::opt<p::seq<token::comma, X>>,
        p::opt<token::comma>
    > {};

    // Operators - these rules do not consume leading whitespace
    struct op {
        struct divide: p::one<'/'> {};
        struct idivide: p::string<'/','/'> {};
        struct multiply: p::one<'*'> {};
        struct plus: p::one<'+'> {};
        struct minus: p::one<'-'> {};
        struct le: p::string<'<','='> {};
        struct ge: p::string<'>','='> {};
        struct lt: p::one<'<'> {};
        struct gt: p::one<'>'> {};
        struct dbleq: p::string<'=','='> {};
        struct ineq: p::string<'!','='> {};
    };

    // Identifiers
    struct identifier: p::seq<
        p::not_at<keyword::rule>,
        p::plus<identifier_char>
    > {};

    // Destructuring patterns
    struct pattern {
        struct rule;
        struct ident: p::seq<prepad<identifier>> {};
        struct opt_slurp: p::seq<token::splat, p::opt<identifier>> {};
        struct def_slurp: p::seq<token::splat, identifier> {};
        struct list {
            struct element: p::seq<rule, p::opt<p::seq<token::equals, expression>>> {};
            struct seq: p::seq<listof_term<element, opt_slurp>> {};
            struct rule: p::seq<token::op_bracket, seq, token::cl_bracket> {};
        };
        struct map {
            struct single_entry: p::seq<prepad<identifier>> {};
            struct entry: p::seq<prepad<identifier>, token::colon, rule> {};
            struct element: p::seq<
                p::sor<entry, single_entry>,
                p::opt<p::seq<token::equals, expression>>
            > {};
            struct seq: p::seq<listof_term<element, def_slurp>> {};
            struct rule: p::seq<token::op_brace, seq, token::cl_brace> {};
        };
        struct rule: prepad<p::sor<ident, list::rule, map::rule>> {};
    };

    // Numbers
    struct number {
        struct decimal: p::one<'.'> {};
        struct sign: p::opt<p::one<'-','+'>> {};
        struct leading: p::sor<p::one<'0'>, p::seq<p::range<'1','9'>, p::star<p::digit>>> {};
        struct trailing: p::plus<p::digit> {};
        struct exponent: p::seq<p::one<'e','E'>, sign, leading> {};
        struct integer: p::seq<sign, leading> {};
        struct float1: p::seq<sign, leading, decimal, p::opt<trailing>, p::opt<exponent>> {};
        struct float2: p::seq<sign, p::opt<leading>, decimal, trailing, p::opt<exponent>> {};
        struct float3: p::seq<sign, leading, exponent> {};
        struct floating: p::sor<float1, float2, float3> {};
        struct rule: p::sor<floating, integer> {};
    };

    // Strings are parsed in two passes:
    // - the first pass identifies the string as a sequence of possibly escaped
    //   characters surrounded by quotes
    // - the second pass divides the string into components, all of which are
    //   either data (regular string literals) or interpolations (expressions)
    // The result of the second pass is converted into AST
    struct string {
        struct interpolate: p::string<'$','{'> {};
        struct quote: p::one<'"'> {};

        // First pass
        struct escaped_unicode: p::seq<p::one<'u'>, p::rep<4, p::xdigit>> {};
        struct escaped: p::sor<
            p::one<'\\', '"', 'b', 'f', 'n', 'r', 't', '$'>,
            escaped_unicode
        > {};
        struct unescaped: p::utf8::range<0x20, 0x10ffff> {};
        struct character: p::if_then_else<p::one<'\\'>, escaped, unescaped> {};
        struct pre: p::until<p::at<quote>, character> {};

        // Second pass
        struct data: p::seq<character, p::until<p::at<p::sor<p::eof, interpolate>>, character>> {};
        struct interp: p::seq<prepad<expression>, prepad<token::cl_brace>> {};
        struct post: p::until<p::eof, p::if_then_else<interpolate, interp, data>> {};

        struct rule: p::seq<quote, p::rematch<pre, p::seq<post, p::eof>>, quote> {};
    };

    // Booleans
    struct boolean: p::sor<keyword::True, keyword::False> {};

    // Lists
    struct list {
        struct element;
        struct loop: p::seq<
            prepad<keyword::For>, pattern::rule, prepad<keyword::In>,
            expression, token::colon, element
        > {};
        struct cond: p::seq<prepad<keyword::If>, expression, token::colon, element> {};
        struct element: p::sor<loop, cond, splatted, expression> {};
        struct seq: p::seq<listof<element>> {};
        struct rule: p::seq<token::op_bracket, seq, token::cl_bracket> {};
    };

    // Maps
    struct map {
        struct element;
        struct const_identifier: p::plus<p::sor<identifier_char, p::one<'-'>>> {};
        struct var_identifier: p::seq<token::dollar, expression> {};
        struct identifier: p::sor<var_identifier, const_identifier> {};
        struct entry: p::seq<prepad<identifier>, token::colon, expression> {};
        struct loop: p::seq<
            prepad<keyword::For>, pattern::rule, prepad<keyword::In>,
            expression, token::colon, element
        > {};
        struct cond: p::seq<prepad<keyword::If>, expression, token::colon, entry> {};
        struct element: p::sor<loop, cond, splatted, entry> {};
        struct seq: p::seq<listof<element>> {};
        struct rule: p::seq<token::op_brace, seq, token::cl_brace> {};
    };

    // Blocks
    struct block {
        struct binding: p::seq<
            prepad<keyword::Let>,
            pattern::rule,
            token::equals,
            expression
        > {};
        struct rule: p::seq<
            binding,
            p::star<binding>,
            prepad<keyword::In>,
            expression
        > {};
    };

    // Functions
    struct func {
        struct param_list: listof<pattern::rule> {};
        struct bracketed_param_list: p::seq<token::op_paren, param_list, token::cl_paren> {};
        struct rule: p::seq<
            bracketed_param_list,
            token::implies,
            expression
        > {};
    };

    // Conditionals
    struct branch: p::seq<
        prepad<keyword::If>,
        expression,
        prepad<keyword::Then>,
        expression,
        prepad<keyword::Else>,
        expression
    > {};

    // Parenthesised expressions
    struct paren: p::seq<
        token::op_paren,
        expression,
        token::cl_paren,
        p::not_at<token::implies>
    > {};

    // Atomic expressions (can have postfix operators)
    struct atomic: prepad<p::sor<
        string::rule,
        number::rule,
        list::rule,
        map::rule,
        identifier,
        boolean,
        keyword::Null,
        paren
    >> {};

    // Precedence level: postfix operators
    struct postfix {
        struct funcall_args: listof<expression> {};
        struct funcall_operator: p::seq<token::op_paren, funcall_args, token::cl_paren> {};
        struct object_access: p::seq<token::dot, identifier> {};
        struct subscript_operator: p::seq<token::op_bracket, expression, token::cl_bracket> {};

        struct post_op: p::sor<
            funcall_operator,
            object_access,
            subscript_operator
        > {};
        struct rule: p::seq<atomic, p::star<post_op>> {};
    };

    // Special case: splat expressions
    struct splatted: p::seq<token::splat, postfix::rule> {};

    // Composite expressions (can't have postfix operators)
    struct composite: p::sor<
        postfix::rule,
        func::rule,
        block::rule,
        branch
    > {};

    // Left-associative operator sequence template
    template <typename T, typename O>
    struct lbinop {
        struct operand: p::seq<T> {};
        struct optor: O {};
        struct operation: p::list<operand, prepad<optor>> {};
    };

    // Binary operator precedence levels (left-to-right)
    struct product: lbinop<postfix::rule, p::sor<op::idivide, op::multiply, op::divide>> {};
    struct sum: lbinop<product::operation, p::sor<op::plus, op::minus>> {};
    struct ineq: lbinop<sum::operation, p::sor<op::le, op::ge, op::lt, op::gt>> {};
    struct eq: lbinop<ineq::operation, p::sor<op::dbleq, op::ineq>> {};
    struct conj: lbinop<eq::operation, keyword::And> {};
    struct disj: lbinop<conj::operation, keyword::Or> {};

    // Finalize
    struct expression: p::seq<p::sor<disj::operation, composite>> {};
    struct file: p::seq<p::bof, expression, prepad<p::eof>> {};

    template<typename Rule>
    using selector = p::parse_tree::selector<Rule,
        p::parse_tree::store_content::on<
            number::rule,
            number::integer,
            number::floating,
            string::post,
            string::data,
            string::interp,
            keyword::Null,
            boolean,
            list::loop,
            list::cond,
            list::seq,
            splatted,
            map::const_identifier,
            map::var_identifier,
            map::entry,
            map::loop,
            map::cond,
            map::seq,
            pattern::ident,
            pattern::opt_slurp,
            pattern::def_slurp,
            pattern::map::single_entry,
            pattern::map::entry,
            pattern::map::element,
            pattern::map::seq,
            pattern::list::element,
            pattern::list::seq,
            block::rule,
            block::binding,
            identifier,
            func::param_list,
            func::rule,
            branch,
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
            postfix::rule,
            postfix::funcall_operator,
            postfix::object_access,
            postfix::subscript_operator,
            file
        >
    >;
}


bool Gold::analyze_grammar() {
    return p::analyze<Grammar::file>() == 0;
}


void Gold::debug_parse(std::string input) {
    p::string_input in(input, "x");
    p::standard_trace<Grammar::file>(in);
}


void Gold::debug_parse_tree(std::string input) {
    p::string_input in(input, "x");
    auto tree = p::parse_tree::parse<Grammar::file, Grammar::selector>(in);
    if (tree) {
        p::parse_tree::print_dot(std::cout, *tree);
        auto ast = normalize(*tree);
        std::cout << *ast << std::endl;
    }
}


template <typename I>
static AstPtr _parse(I& input) {
    try {
        auto tree = p::parse_tree::parse<Grammar::file, Grammar::selector>(input);
        if (!tree)
            throw ParseException();
        return normalize(*tree);
    }
    catch (const p::parse_error&) {
        throw ParseException();
    }
}


AstPtr Gold::parse_string(std::string code) {
    p::string_input in(code, "code");
    return _parse(in);
}


AstPtr Gold::parse_file(std::string path) {
    p::file_input in(path, "code");
    return _parse(in);
}


Object Gold::evaluate_string(std::string code) {
    EvaluationContext ctx;
    return evaluate_string(ctx, code);
}


Object Gold::evaluate_string(EvaluationContext& ctx, std::string code) {
    auto ast = parse_string(code);
    auto value = ast->evaluate(ctx);
    return value;
}


Object Gold::evaluate_file(std::string code) {
    EvaluationContext ctx;
    return evaluate_file(ctx, code);
}


Object Gold::evaluate_file(EvaluationContext& ctx, std::string path) {
    auto ast = parse_file(path);
    auto value = ast->evaluate(ctx);
    return value;
}
