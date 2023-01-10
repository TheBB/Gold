use std::fmt::Debug;
use std::num::{ParseFloatError, ParseIntError};
use std::ops::Deref;

use num_bigint::ParseBigIntError;
use num_bigint::BigInt;

use nom::{
    IResult, Parser as NomParser, Err as NomError,
    branch::alt,
    combinator::{map, map_res, opt, verify},
    error::{ErrorKind, ParseError, FromExternalError, ContextError},
    multi::{many0, many1},
    sequence::{delimited, preceded, terminated, tuple},
};

use crate::ast::*;
use crate::error::{Error, Span, Tagged, Syntax, SyntaxError, SyntaxElement};
use crate::lexing::{Lexer, TokenType, CachedLexer, CachedLexResult};
use crate::object::{Object, Key};
use crate::traits::{Boxable, Taggable, Validatable};


trait ExplainError {
    fn error<'a, T>(lex: CachedLexer<'a>, reason: T) -> Self where Syntax: From<T>;
}

impl ExplainError for SyntaxError {
    fn error<'a, T>(lex: CachedLexer<'a>, reason: T) -> Self where Syntax: From<T> {
        lex.error(Syntax::from(reason))
    }
}

impl<'a> ParseError<In<'a>> for SyntaxError {
    fn from_error_kind(lex: In<'a>, _: ErrorKind) -> Self {
        Self::new(lex.position(), None)
    }

    fn from_char(lex: In<'a>, _: char) -> Self {
        Self::new(lex.position(), None)
    }

    fn append(_: In<'a>, _: ErrorKind, other: Self) -> Self {
        other
    }
}

impl<'a> ContextError<In<'a>> for SyntaxError {
    fn add_context(_: In<'a>, _: &'static str, other: Self) -> Self {
        other
    }
}

impl<'a> FromExternalError<In<'a>, ParseIntError> for SyntaxError {
    fn from_external_error(lex: In<'a>, _: ErrorKind, _: ParseIntError) -> Self {
        Self::new(lex.position(), None)
    }
}

impl<'a> FromExternalError<In<'a>, ParseBigIntError> for SyntaxError {
    fn from_external_error(lex: In<'a>, _: ErrorKind, _: ParseBigIntError) -> Self {
        Self::new(lex.position(), None)
    }
}

impl<'a> FromExternalError<In<'a>, ParseFloatError> for SyntaxError {
    fn from_external_error(lex: In<'a>, _: ErrorKind, _: ParseFloatError) -> Self {
        Self::new(lex.position(), None)
    }
}


// fn literal<T>(x: T) -> Expr where Object: From<T> {
//     Object::from(x).literal()
// }


/// Convert a multiline string from source code to string by removing leading
/// whitespace from each line according to the rules for such strings.
fn multiline(s: &str) -> String {
    let mut lines = s.lines();

    let first = lines.next().unwrap().trim_start();

    let rest: Vec<&str> = lines.filter(|s: &&str| !s.deref().trim().is_empty()).collect();
    let indent =
        rest.iter()
            .filter(|s: &&&str| !s.trim().is_empty())
            .map(|s: &&str| s.deref().chars().take_while(|c| c.is_whitespace()).map(|_| 1).sum())
            .min().unwrap_or(0);

    let mut ret = first.to_string();
    for r in rest {
        if !ret.is_empty() {
            ret += "\n";
        }
        ret += &r.chars().skip(indent).collect::<String>();
    }

    ret
}


/// Temporary expression wrapper used for accurately tracking parenthesized
/// locations.
///
/// For parenthesized expressions, the Gold parser keeps track of both the outer
/// and the inner locations, whereas for non-parenthesized expressions, only the
/// inner location is tracked.
///
/// ```ignore
/// ( some_expression_here )
///   ^----- inner ------^
/// ^------- outer --------^
/// ```
///
/// In this way, when a parenthesized expression becomes a constituent part of
/// a larger expression, the parentheses can be included on both sides, by using
/// the outer span, e.g.:
///
/// ```ignore
/// ( 2 + 3 ) * 5
/// ^-----------^
/// ```
///
/// Instead of the confusing result that would result from using the inner span,
/// incorrectly giving the impression that imbalanced parentheses are allowed:
///
/// ```ignore
/// ( 2 + 3 ) * 5
///   ^---------^
/// ```
///
/// On the other hand, when a parenthesised expression is used in a context where
/// an error originates purely from the inner expression, Gold can disregard the
/// parentheses when reporting the error:
///
/// ```ignore
/// let x = ( some_function(y) ) in x + x
///           ^--------------^
/// ```
#[derive(Clone, Debug)]
enum Paren<T> {
    /// A naked (non-parenthesized) expression.
    Naked(Tagged<T>),

    /// A parenthesized expression with two layers of location tags: outer and inner.
    Parenthesized(Tagged<Tagged<T>>),
}


impl<T> Paren<T> {
    /// Return the inner expression with location tag, disregarding potential
    /// parentheses.
    fn inner(self) -> Tagged<T> {
        match self {
            Self::Naked(x) => x,
            Self::Parenthesized(x) => x.unwrap(),
        }
    }

    /// Return the outermost location span, either parenthesized or not.
    ///
    /// Use this when combining two spans.
    fn outer(&self) -> Span {
        match self {
            Self::Naked(x) => x.span(),
            Self::Parenthesized(x) => x.span(),
        }
    }

    fn map_wrap<F, U>(self, f: F) -> Paren<U> where F: FnOnce(Tagged<T>) -> U {
        match self {
            Self::Naked(x) => Paren::<U>::Naked(x.wrap(f)),
            Self::Parenthesized(x) => Paren::<U>::Parenthesized(x.map(|y| y.wrap(f))),
        }
    }
}


type PExpr = Paren<Expr>;
type PList = Paren<ListElement>;
type PMap = Paren<MapElement>;

type OpCons = fn(Tagged<Expr>, loc: Span) -> Operator;

type In<'a> = CachedLexer<'a>;
type Out<'a, T> = IResult<In<'a>, T, SyntaxError>;

trait Parser<'a, T>: NomParser<In<'a>, T, SyntaxError> {}
impl<'a, T, P> Parser<'a, T> for P where P: NomParser<In<'a>, T, SyntaxError> {}


/// Convert errors to failures.
fn fail<'a, O, T>(
    mut parser: impl Parser<'a, O>,
    reason: T,
) -> impl Parser<'a, O>
where Syntax: From<T>, T: Copy
{
    move |input: In<'a>| {
        parser.parse(input.clone()).map_err(
            |err| match err {
                NomError::Failure(e) => NomError::Failure(e),
                NomError::Error(_) => {
                    NomError::Failure(SyntaxError::error(input, reason))
                },
                _ => err
            }
        )
    }
}


/// Apply a separator skip rule to an item parser. See [`seplist_opt_delim`] for
/// details.
fn apply_skip<'a, O>(
    parser: impl Parser<'a, O>,
    skip_delimiter: bool,
) -> impl Parser<'a, (O, bool)> {
    map(parser, move |x| (x, skip_delimiter))
}


/// Create an item parser that always skips the following separator. See
/// [`seplist_opt_delim`] for details.
fn do_skip<'a, O>(
    parser: impl Parser<'a, O>,
) -> impl Parser<'a, (O, bool)> {
    apply_skip(parser, true)
}


/// Create an item parser that never skips the following separator. See
/// [`seplist_opt_delim`] for details.
fn dont_skip<'a, O>(
    parser: impl Parser<'a, O>,
) -> impl Parser<'a, (O, bool)> {
    apply_skip(parser, false)
}


/// Separated list with delimiters and optional trailing separator.
///
/// The item parser should return a tuple with two items: the item itself, and a
/// boolean indicating whether the following separator should be skipped or not.
/// This is used in certain contexts, like map parsing.
fn seplist_opt_delim<'a, Init, Item, Sep, Term, InitR, ItemR, SepR, TermR, T, U>(
    mut initializer: Init,
    mut item: Item,
    mut separator: Sep,
    mut terminator: Term,
    err_terminator_or_item: T,
    err_terminator_or_separator: U,
) -> impl Parser<'a, (InitR, Vec<ItemR>, TermR)>
where
    Init: Parser<'a, InitR>,
    Item: Parser<'a, (ItemR, bool)>,
    Sep: Parser<'a, SepR>,
    Term: Parser<'a, TermR>,
    Syntax: From<T> + From<U>,
    T: Copy,
    U: Copy,
    ItemR: Debug,
{
    move |mut i: In<'a>| {
        let (j, initr) = initializer.parse(i)?;
        i = j;

        let mut items = Vec::new();
        let mut expect_separator: bool;

        loop {

            // println!("at {:?}", i.code);

            let u = item.parse(i.clone());
            // println!("u = {:?}", u);

            // Try to parse an item
            match u {

                // Parsing item failed: we expect a terminator
                Err(NomError::Error(_)) => {
                    // println!("fail :-(");
                    match terminator.parse(i.clone()) {
                        Err(NomError::Error(_)) => return Err(NomError::Failure(
                            SyntaxError::error(i, err_terminator_or_item)
                        )),
                        Err(e) => return Err(e),
                        Ok((i, termr)) => return Ok((i, (initr, items, termr))),
                    }
                }

                // Parsing item failed irrecoverably
                Err(e) => return Err(e),

                // Parsing item succeeded
                Ok((j, (it, skip_separator))) => {
                    // println!("yay? :-s");
                    i = j;
                    expect_separator = !skip_separator;
                    items.push(it);
                }
            }

            // If at this moment we don't expect a separator, try to parse a terminator
            if !expect_separator {
                match terminator.parse(i.clone()) {
                    Err(NomError::Error(_)) => { },
                    Err(e) => { return Err(e); },
                    Ok((i, termr)) => return Ok((i, (initr, items, termr))),
                }

                continue;
            }

            // Try to parse a separator
            match separator.parse(i.clone()) {

                // Parsing separator failed: we expect a terminator
                Err(NomError::Error(_)) => {
                    match terminator.parse(i.clone()) {
                        Err(NomError::Error(_)) => return Err(NomError::Failure(
                            SyntaxError::error(i, err_terminator_or_separator)
                        )),
                        Err(e) => return Err(e),
                        Ok((i, termr)) => return Ok((i, (initr, items, termr))),
                    }
                }

                // Parsing separator failed irrecoverably
                Err(e) => return Err(e),

                // Parsing separator succeeded
                Ok((j, _)) => { i = j; }
            }

        }

    }
}


/// Separated list with delimiters and optional trailing separator.
fn seplist<'a, Init, Item, Sep, Term, InitR, ItemR, SepR, TermR, T, U>(
    initializer: Init,
    item: Item,
    separator: Sep,
    terminator: Term,
    err_terminator_or_item: T,
    err_terminator_or_separator: U,
) -> impl Parser<'a, (InitR, Vec<ItemR>, TermR)>
where
    Init: Parser<'a, InitR>,
    Item: Parser<'a, ItemR>,
    Sep: Parser<'a, SepR>,
    Term: Parser<'a, TermR>,
    Syntax: From<T> + From<U>,
    T: Copy,
    U: Copy,
    ItemR: Debug,
{
    let item_parser = map(item, |it| (it, false));
    seplist_opt_delim(initializer, item_parser, separator, terminator, err_terminator_or_item, err_terminator_or_separator)
}


/// Wrap the output of a parser in Paren::Naked.
fn naked<'a, U>(
    parser: impl Parser<'a, Tagged<U>>,
) -> impl Parser<'a, Paren<U>> {
    map(parser, Paren::Naked)
}


/// Never failing parser that obtains the current column.  Useful for
/// indentation-sensitive rules.
fn column<'a>(input: In<'a>) -> Out<'a, u32> {
    let col = input.position().column();
    Ok((input, col))
}


fn token<'a>(
    getter: impl Fn(In<'a>) -> CachedLexResult<'a>,
    kind: TokenType,
) -> impl Parser<'a, Tagged<&'a str>> {
    move |lex: In<'a>| {
        let (lex, tok) = getter(lex).map_err(NomError::Error)?;
        if tok.as_ref().kind == kind {
            Ok((lex, tok.as_ref().text.tag(&tok)))
        } else {
            Err(NomError::Error(SyntaxError::error(lex, kind)))
        }
    }
}


macro_rules! tok {
    ($pname:ident, $toktype:ident) => {
        fn $pname<'a>(input: In<'a>) -> Out<Tagged<&'a str>> {
            token(CachedLexer::next_token, TokenType::$toktype).parse(input)
        }
    };

    ($pname:ident, $toktype:ident, $getter:ident) => {
        fn $pname<'a>(input: In<'a>) -> Out<Tagged<&'a str>> {
            token(CachedLexer::$getter, TokenType::$toktype).parse(input)
        }
    };
}


tok!{name, Name}
tok!{float, Float}
tok!{integer, Integer}

tok!{asterisk, Asterisk}
tok!{caret, Caret}
tok!{close_brace, CloseBrace}
tok!{close_brace_pipe, CloseBracePipe}
tok!{close_bracket, CloseBracket}
tok!{close_paren, CloseParen}
tok!{colon, Colon}
tok!{comma, Comma}
tok!{dot, Dot}
tok!{double_eq, DoubleEq}
tok!{double_quote, DoubleQuote}
tok!{double_slash, DoubleSlash}
tok!{ellipsis, Ellipsis}
tok!{eq, Eq}
tok!{exclam_eq, ExclamEq}
tok!{greater_eq, GreaterEq}
tok!{greater, Greater}
tok!{less_eq, LessEq}
tok!{less, Less}
tok!{minus, Minus}
tok!{open_brace, OpenBrace}
tok!{open_brace_pipe, OpenBracePipe}
tok!{open_bracket, OpenBracket}
tok!{open_paren, OpenParen}
tok!{pipe, Pipe}
tok!{plus, Plus}
tok!{semicolon, SemiColon}
tok!{slash, Slash}

tok!{map_name, Name, next_key}
tok!{map_colon, Colon, next_key}
tok!{map_dollar, Dollar, next_key}
tok!{map_double_colon, DoubleColon, next_key}
tok!{map_ellipsis, Ellipsis, next_key}

tok!{string_lit, StringLit, next_string}
tok!{string_dollar, Dollar, next_string}
tok!{string_double_quote, DoubleQuote, next_string}


/// Match a single multiline string starting at a column.
fn multistring<'a>(col: u32) -> impl Parser<'a, Tagged<&'a str>> {
    move |lex: In<'a>| lex.next_multistring(col)
        .map(|(lex, tok)| (lex, tok.as_ref().text.tag(&tok)))
        .map_err(NomError::Error)
}


/// Match a single named keyword. This does not match if the keyword is a prefix
/// of some other name or identifier.
fn keyword_raw<'a>(
    parser: impl Parser<'a, Tagged<&'a str>>,
    value: &'a str,
) -> impl Parser<'a, Tagged<&'a str>> {
    verify(parser, move |out| { *out.as_ref() == value })
}


/// Match a single named keyword. This does not match if the keyword is a prefix
/// of some other name or identifier.
fn keyword<'a>(value: &'a str) -> impl Parser<'a, Tagged<&'a str>> {
    keyword_raw(name, value)
}


/// Match a single named keyword. This does not match if the keyword is a prefix
/// of some other name or identifier.
fn map_keyword<'a>(value: &'a str) -> impl Parser<'a, Tagged<&'a str>> {
    keyword_raw(map_name, value)
}


/// List of keywords that must be avoided by the [`identifier`] parser.
static KEYWORDS: [&'static str; 15] = [
    "for",
    "when",
    "if",
    "then",
    "else",
    "let",
    "in",
    "true",
    "false",
    "null",
    "and",
    "or",
    "not",
    "as",
    "import",
];


/// Match an identfier.
///
/// This parser will refuse to match known keywords (see [`KEYWORDS`]).
fn identifier<'a>(input: In<'a>) -> Out<'a, Tagged<Key>> {
    map(
        verify(name, |out| !KEYWORDS.contains(out.as_ref())),
        |span| span.map(Key::new)
    )(input)
}


/// Match an identifier in a map context.
///
/// Maps have relaxed conditions on identifier names compared to 'regular' code.
fn map_identifier<'a>(input: In<'a>) -> Out<'a, Tagged<Key>> {
    map(map_name, |span| span.map(Key::new))(input)
}


/// Match a number.
fn number<'a>(input: In<'a>) -> Out<'a, PExpr> {
    naked(
        alt((
            map_res(float, |span| span.as_ref().replace('_', "").parse::<f64>().map(|x| Expr::Literal(Object::float(x)).tag(&span))),
            map_res(
                integer,
                |span| {
                    let text = span.as_ref().replace('_', "");
                    let y = text.parse::<i64>().map(Object::int).or_else(
                        |_| text.parse::<BigInt>().map(Object::int)
                    ).map(Expr::Literal);
                    y.map(|x| x.tag(&span))
                },
            ),
        ))
    ).parse(input)
}


/// Matches a raw string part.
///
/// This means all characters up to a terminating symbol: either a closing quote
/// or a dollar sign, signifying the beginning of an interpolated segment. This
/// parser does *not* parse the initial quote or the terminating symbol,
/// whatever that may be.
fn raw_string<'a>(input: In<'a>) -> Out<'a, String> {
    map(
        string_lit,
        |span| {
            let mut out = "".to_string();
            let mut chars = span.as_ref().char_indices();
            loop {
                match chars.next() {
                    Some((_, '\\')) => match chars.next() {
                        Some((_, '\\')) => { out += "\\"; }
                        Some((_, '"')) => { out += "\""; }
                        Some((_, '$')) => { out += "$"; }
                        Some((_, _)) => {
                            // TODO: Calculate accurate error
                            continue;
                        },
                        None => {
                            // TODO: Calculate accurate error
                            break;
                        }
                    },
                    Some((_, c)) => { out.push(c) }
                    None => { break; }
                }
            }

            out
        }
    )(input)
}


/// Matches a non-interpolated string element.
///
/// This is just the output of [`raw_string`] returned as a [`StringElement`].
fn string_data<'a>(input: In<'a>) -> Out<'a, StringElement> {
    map(
        raw_string,
        StringElement::raw,
    )(input)
}


/// Matches an interpolated string element.
fn string_interp<'a>(input: In<'a>) -> Out<'a, StringElement> {
    map(
        delimited(
            terminated(
                string_dollar,
                fail(open_brace, TokenType::OpenBrace),
            ),
            fail(expression, SyntaxElement::Expression),
            fail(close_brace, TokenType::CloseBrace),
        ),

        |x| StringElement::Interpolate(x.inner()),
    )(input)
}


/// Matches a string part.
///
/// This parser matches an opening quote, followed by a sequence of string
/// elements: either raw string data or interpolated expressions, followed by a
/// closing quote.
fn string_part<'a>(input: In<'a>) -> Out<'a, Tagged<Vec<StringElement>>> {
    map(
        tuple((
            double_quote,
            many0(alt((string_interp, string_data))),
            fail(string_double_quote, TokenType::DoubleQuote),
        )),

        |(a, x, b)| x.tag(a.span()..b.span())
    )(input)
}


/// Matches a string.
///
/// This consists of a sequence of one or more string parts, separated by
/// whitespace.
fn string<'a>(input: In<'a>) -> Out<'a, PExpr> {
    naked(map(
        many1(string_part),
        |x| {
            let start = x.first().unwrap().span();
            let end = x.last().unwrap().span();
            let elements: Vec<StringElement> = x.into_iter().map(Tagged::unwrap).flatten().collect();
            Expr::string(elements).tag(start..end)
        }
    )).parse(input)
}


/// Matches a boolean literal.
fn boolean<'a>(input: In<'a>) -> Out<'a, PExpr> {
    naked(alt((
        map(keyword("false"), |tok| Expr::Literal(Object::bool(false)).tag(&tok)),
        map(keyword("true"), |tok| Expr::Literal(Object::bool(true)).tag(&tok)),
    ))).parse(input)
}


/// Matches a null literal.
fn null<'a>(input: In<'a>) -> Out<'a, PExpr> {
    naked(map(keyword("null"), |tok| Expr::Literal(Object::null()).tag(&tok))).parse(input)
}


/// Matches any atomic (non-divisible) expression.
///
/// Although strings are technically not atomic due to possibly interpolated
/// expressions.
fn atomic<'a>(input: In<'a>) -> Out<'a, PExpr> {
    alt((
        null,
        boolean,
        number,
        string,
        naked(map(identifier, |x| x.wrap(Expr::Identifier)))
    ))(input)
}


/// Matches a list element: anything that is legal in a list.
///
/// There are four cases:
/// - singleton elements: `[2]`
/// - splatted iterables: `[...x]`
/// - conditional elements: `[if cond: @]`
/// - iterated elements: `[for x in y: @]`
fn list_element<'a>(input: In<'a>) -> Out<'a, PList> {
    alt((

        // Splat
        naked(map(
            tuple((
                ellipsis,
                fail(expression, SyntaxElement::Expression),
            )),
            |(start, expr)| {
                let span = start.span()..expr.outer();
                ListElement::Splat(expr.inner()).tag(span)
            },
        )),

        // Iteration
        naked(map(
            tuple((
                keyword("for"),
                fail(binding, SyntaxElement::Binding),
                preceded(
                    fail(keyword("in"), SyntaxElement::In),
                    fail(expression, SyntaxElement::Expression),
                ),
                preceded(
                    fail(colon, TokenType::Colon),
                    fail(list_element, SyntaxElement::ListElement)
                ),
            )),
            |(start, binding, iterable, expr)| {
                let span = start.span()..expr.outer();
                ListElement::Loop {
                    binding,
                    iterable: iterable.inner(),
                    element: Box::new(expr.inner()),
                }.tag(span)
            }
        )),

        // Conditional
        naked(map(
            tuple((
                keyword("when"),
                fail(expression, SyntaxElement::Expression),
                preceded(
                    fail(colon, TokenType::Colon),
                    fail(list_element, SyntaxElement::ListElement),
                ),
            )),
            |(start, condition, expr)| {
                let span = start.span()..expr.outer();
                ListElement::Cond {
                    condition: condition.inner(),
                    element: Box::new(expr.inner()),
                }.tag(span)
            },
        )),

        // Singleton
        map(expression, |x| x.map_wrap(ListElement::Singleton))

    ))(input)
}


/// Matches a list.
///
/// A list is composed of an opening bracket, a potentially empty
/// comma-separated list of list elements, an optional terminal comma and a
/// closing bracket.
fn list<'a>(input: In<'a>) -> Out<'a, PExpr> {
    naked(map(
        seplist(
            open_bracket,
            list_element,
            comma,
            close_bracket,
            (TokenType::CloseBracket, SyntaxElement::ListElement),
            (TokenType::CloseBracket, TokenType::Comma),
        ),

        |(a, x, b)| Expr::List(x.into_iter().map(|y| y.inner()).collect()).tag(a.span()..b.span()),
    )).parse(input)
}


/// Matches a singleton key in a map context.
///
/// This is either a dollar sign followed by an expression, a string literal or
/// a pure map identifier.
fn map_key_singleton<'a>(input: In<'a>) -> Out<'a, (u32, PExpr)> {
    tuple((
        column,

        alt((
            map(
                tuple((
                    map_dollar,
                    fail(expression, SyntaxElement::Expression),
                )),
                |(d, ex)| {
                    let span = d.span()..ex.outer();
                    PExpr::Parenthesized(ex.inner().tag(span))
                }
            ),

            string,

            naked(map(
                map_identifier,
                |key| key.map(Object::key).map(Expr::Literal),
            )),
        ))
    ))(input)
}


/// Matches a singleton value in a map context.
///
/// This is either a double colon followed by a multiline string, or a single
/// comma followed by an expression.
fn map_value_singleton<'a>(col: u32, input: In<'a>) -> Out<'a, (PExpr, bool)> {
    alt((
        do_skip(naked(map(
            preceded(
                map_double_colon,
                multistring(col),
            ),
            |s| s.map(|s| Expr::string(vec![StringElement::raw(multiline(s.as_ref()))])),
        ))),

        dont_skip(preceded(
            fail(map_colon, TokenType::Colon),
            fail(expression, SyntaxElement::Expression),
        )),
    ))(input)
}


/// Matches a singleton map element: a singleton key followed by a singleton
/// value.
fn map_element_singleton<'a>(input: In<'a>) -> Out<'a, (PMap, bool)> {
    let input = input.skip_whitespace();
    let (input, (col, key)) = map_key_singleton(input)?;
    let (input, (value, skip_sep)) = map_value_singleton(col, input)?;

    let span = key.outer()..value.outer();
    let ret = MapElement::Singleton { key: key.inner(), value: value.inner() }.tag(span);

    Ok((input, (PMap::Naked(ret), skip_sep)))
}


/// Matches a map element: anything that is legal in a map.
///
/// There are five cases:
/// - singleton elements
/// - splatted iterables: `{...x}`
/// - conditional elements: `{if cond: @}`
/// - iterated elements: `{for x in y: @}`
fn map_element<'a>(input: In<'a>) -> Out<'a, (PMap, bool)> {
    alt((

        // Splat
        dont_skip(naked(map(
            tuple((
                map_ellipsis,
                fail(expression, SyntaxElement::Expression),
            )),
            |(start, expr)| {
                let span = start.span()..expr.outer();
                MapElement::Splat(expr.inner()).tag(span)
            },
        ))),

        // Iteration
        map(
            tuple((
                map_keyword("for"),
                fail(binding, SyntaxElement::Binding),
                preceded(
                    fail(keyword("in"), SyntaxElement::In),
                    fail(expression, SyntaxElement::Expression),
                ),
                preceded(
                    fail(colon, TokenType::Colon),
                    fail(map_element, SyntaxElement::MapElement),
                ),
            )),
            |(start, binding, iterable, (expr, skip))| {
                let span = start.span()..expr.outer();
                let ret = MapElement::Loop {
                    binding,
                    iterable: iterable.inner(),
                    element: Box::new(expr.inner()),
                }.tag(span);
                (PMap::Naked(ret), skip)
            },
        ),

        // Conditional
        map(
            tuple((
                map_keyword("when"),
                fail(expression, SyntaxElement::Expression),
                preceded(
                    fail(colon, TokenType::Colon),
                    fail(map_element, SyntaxElement::MapElement),
                ),
            )),
            |(start, condition, (expr, skip))| {
                let span = start.span()..expr.outer();
                let ret = MapElement::Cond {
                    condition: condition.inner(),
                    element: Box::new(expr.inner())
                }.tag(span);
                (PMap::Naked(ret), skip)
            },
        ),

        // Various types of singletons
        map_element_singleton,

    ))(input)
}



/// Matches a map.
///
/// A list is composed of an opening brace, a potentially empty comma-separated
/// list of map elements, an optional terminal comma and a closing brace.
fn mapping<'a>(input: In<'a>) -> Out<'a, PExpr> {
    naked(map(
        seplist_opt_delim(
            open_brace,
            map_element,
            comma,
            close_brace,
            (TokenType::CloseBrace, SyntaxElement::MapElement),
            (TokenType::CloseBrace, TokenType::Comma),
        ),

        |(a, x, b)| Expr::Map(x.into_iter().map(|y| y.inner()).collect()).tag(a.span()..b.span()),
    )).parse(input)
}


/// Matches a parenthesized expression.
///
/// This is the only possible source of Paren::Parenthesized in the Gold
/// language. All other parenthesized variants stem from this origin.
fn paren<'a>(input: In<'a>) -> Out<'a, PExpr> {
    map(
        tuple((
            open_paren,
            fail(expression, SyntaxElement::Expression),
            fail(close_paren, TokenType::CloseParen),
        )),

        |(start, expr, end)| PExpr::Parenthesized(expr.inner().tag(start.span()..end.span()))
    )(input)
}


/// Matches an expression that can be an operand.
///
/// The tightest binding operators are the postfix operators, so this class of
/// expressions are called 'postixable' expressions. Only expressions with a
/// well defined end are postfixable: in particular, functions, let-blocks and
/// tertiary expressions are not postfixable, but parenthesized expressions are.
fn postfixable<'a>(input: In<'a>) -> Out<'a, PExpr> {
    alt((
        paren,
        atomic,
        naked(map(identifier, |x| Expr::Identifier(x).tag(&x))),
        list,
        mapping,
    ))(input)
}


/// Matches a dot-syntax subscripting operator.
///
/// This is a dot followed by an identifier.
fn object_access<'a>(input: In<'a>) -> Out<'a, Tagged<Operator>> {
    map(
        tuple((dot, fail(identifier, SyntaxElement::Identifier))),
        |(dot, out)| Operator::BinOp(
            BinOp::Index.tag(&dot),
            out.map(Object::key).map(Expr::Literal).to_box(),
        ).tag(dot.span()..out.span()),
    )(input)
}


/// Matches a bracket-syntax subscripting operator.
///
/// This is an open bracket followed by any expression and a closing bracket.
fn object_index<'a>(input: In<'a>) -> Out<'a, Tagged<Operator>> {
    map(
        tuple((
            open_bracket,
            fail(expression, SyntaxElement::Expression),
            fail(close_bracket, TokenType::CloseBracket),
        )),
        |(a, expr, b)| {
            let span = Span::from(a.span()..b.span());
            Operator::BinOp(BinOp::Index.tag(span), expr.inner().to_box()).tag(span)
        },
    )(input)
}


/// Matches a function argument element.
///
/// There are three cases:
/// - splatted iterables: `f(...x)`
/// - keyword arguments: `f(x: y)`
/// - singleton arguments: `f(x)`
fn function_arg<'a>(input: In<'a>) -> Out<'a, Tagged<ArgElement>> {
    alt((

        // Splat
        map(
            tuple((
                ellipsis,
                fail(expression, SyntaxElement::Expression),
            )),
            |(x, y)| {
                let span = x.span()..y.outer();
                ArgElement::Splat(y.inner()).tag(span)
            }
        ),

        // Keyword
        map(
            tuple((
                identifier,
                preceded(
                    colon,
                    fail(expression, SyntaxElement::Expression),
                ),
            )),
            |(name, expr)| {
                let span = name.span()..expr.outer();
                ArgElement::Keyword(name, expr.inner()).tag(span)
            },
        ),

        // Singleton
        map(
            expression,
            |x| {
                let span = x.outer();
                ArgElement::Singleton(x.inner()).tag(span)
            },
        ),

    ))(input)
}


/// Matches a function call operator.
///
/// This is an open parenthesis followed by a possibly empty list of
/// comma-separated argument elements, followed by an optional comma and a
/// closin parenthesis.
fn function_call<'a>(input: In<'a>) -> Out<'a, Tagged<Operator>> {
    map(
        seplist(
            open_paren,
            function_arg,
            comma,
            close_paren,
            (TokenType::CloseParen, SyntaxElement::ArgElement),
            (TokenType::CloseParen, TokenType::Comma),
        ),
        |(a, expr, b)| {
            let span = Span::from(a.span()..b.span());
            Operator::FunCall(expr.tag(span)).tag(span)
        },
    )(input)
}


/// Matches any postfix operator expression.
///
/// This is a postfixable expression (see [`postfixable`]) followed by an
/// arbitrary sequence of postfix operators.
fn postfixed<'a>(input: In<'a>) -> Out<'a, PExpr> {
    map(
        tuple((
            postfixable,
            many0(alt((
                object_access,
                object_index,
                function_call,
            ))),
        )),

        |(expr, ops)| {
            ops.into_iter().fold(
                expr,
                |expr, operator| {
                    let span = expr.outer()..operator.span();
                    PExpr::Naked(Expr::Operator {
                        operand: Box::new(expr.inner()),
                        operator: operator.unwrap()
                    }.tag(span))
                },
            )
        },
    )(input)
}


/// Matches any prefixed operator expression.
///
/// This is an arbitrary sequence of prefix operators followed by a postfixed
/// expression.
fn prefixed<'a>(input: In<'a>) -> Out<'a, PExpr> {
    alt((
        power,

        map(
            tuple((
                many1(alt((
                    map(plus, |x| x.map(|_| UnOp::Passthrough)),
                    map(minus, |x| x.map(|_| UnOp::ArithmeticalNegate)),
                    map(keyword("not"), |x| x.map(|_| UnOp::LogicalNegate)),
                ))),
                fail(power, SyntaxElement::Operand),
            )),

            |(ops, expr)| {
                ops.into_iter().rev().fold(
                    expr,
                    |expr, operator| {
                        let span = operator.span()..expr.outer();
                        PExpr::Naked(Expr::Operator {
                            operand: Box::new(expr.inner()),
                            operator: Operator::UnOp(operator)
                        }.tag(span))
                    },
                )
            },
        )
    ))(input)
}


/// Utility parser for parsing a single binary operator with operand.
///
/// `operators` should return, loosely, a function Expr -> Operator.
/// `operand` should return an Expr.
///
/// The result, essentially, is the result of `operators` applied to the result
/// of `operand`, thus, an Operator.
///
/// Note that in the Gold abstract syntax tree model, an operator is anything
/// that 'acts' on an expression. In this interpretation, in an expression such
/// as `1 + 2`, `+ 2` is the operator that acts on `1`.
fn binop<'a>(
    operators: impl Parser<'a, Tagged<OpCons>>,
    operand: impl Parser<'a, PExpr>,
) -> impl Parser<'a, Tagged<Operator>> {
    map(
        tuple((
            operators,
            fail(operand, SyntaxElement::Operand),
        )),
        |(func, expr)| {
            let span = func.span()..expr.outer();
            func.as_ref()(expr.inner(), func.span()).direct_tag(span)
        },
    )
}


/// Utility parser for parsing a left- or right-associative sequence of operators.
///
/// `operators` is normally a parser created by [`binop`], that is, something
/// that returns an `Operator`.
fn binops<'a>(
    operators: impl Parser<'a, Tagged<Operator>>,
    operand: impl Parser<'a, PExpr>,
    right: bool,
) -> impl Parser<'a, PExpr> {
    map(
        tuple((
            operand,
            many0(operators),
        )),
        move |(expr, ops)| {
            let acc = |expr: PExpr, operator: Tagged<Operator>| {
                let span = expr.outer()..operator.span();
                PExpr::Naked(Expr::Operator {
                    operand: Box::new(expr.inner()),
                    operator: operator.unwrap(),
                }.tag(span))
            };
            if right {
                ops.into_iter().rev().fold(expr, acc)
            } else {
                ops.into_iter().fold(expr, acc)
            }
        },
    )
}


/// Matches the exponentiation precedence level.
///
/// The exponentiation operator, unlike practically every other operator, is
/// right-associative, and asymmetric in its operands: it binds tighter than
/// prefix operators on the left, but not on the right.
fn power<'a>(input: In<'a>) -> Out<'a, PExpr> {
    binops(
        binop(
            alt((
                map(caret, |x| (Operator::power as OpCons).tag(&x)),
            )),
            prefixed,
        ),
        postfixed,
        true,
    ).parse(input)
}


/// Utility parser for matching a sequence of left-associative operators with
/// symmetric operands. In other words, most conventional operators.
fn lbinop<'a>(
    operators: impl Parser<'a, Tagged<OpCons>>,
    operands: impl Parser<'a, PExpr> + Copy,
) -> impl Parser<'a, PExpr> {
    binops(binop(operators, operands), operands, false)
}


/// Matches the multiplication precedence level.
fn product<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((
            map(asterisk, |x| (Operator::multiply as OpCons).tag(&x)),
            map(double_slash, |x| (Operator::integer_divide as OpCons).tag(&x)),
            map(slash, |x| (Operator::divide as OpCons).tag(&x)),
        )),
        prefixed,
    ).parse(input)
}


/// Matches the addition predecence level.
fn sum<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((
            map(plus, |x| (Operator::add as OpCons).tag(&x)),
            map(minus, |x| (Operator::subtract as OpCons).tag(&x)),
        )),
        product,
    ).parse(input)
}


/// Matches the inequality comparison precedence level.
fn inequality<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((
            map(less_eq, |x| (Operator::less_equal as OpCons).tag(&x)),
            map(less, |x| (Operator::less as OpCons).tag(&x)),
            map(greater_eq, |x| (Operator::greater_equal as OpCons).tag(&x)),
            map(greater, |x| (Operator::greater as OpCons).tag(&x)),
        )),
        sum,
    ).parse(input)
}


/// Matches the equality comparison precedence level.
fn equality<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((
            map(double_eq, |x| (Operator::equal as OpCons).tag(&x)),
            map(exclam_eq, |x| (Operator::not_equal as OpCons).tag(&x)),
        )),
        inequality,
    ).parse(input)
}


/// Matches the conjunction ('and') precedence level.
fn conjunction<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((
            map(keyword("and"), |x| (Operator::and as OpCons).tag(&x)),
        )),
        equality,
    ).parse(input)
}


/// Matches the disjunction ('or') precedence level.
fn disjunction<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((
            map(keyword("or"), |x| (Operator::or as OpCons).tag(&x)),
        )),
        conjunction,
    ).parse(input)
}


/// Matches an identifier binding. This is essentially the same as a normal
/// identifier.
fn ident_binding<'a>(input: In<'a>) -> Out<'a, Tagged<Binding>> {
    alt((
        map(
            identifier,
            |out| Binding::Identifier(out).tag(&out),
        ),
    ))(input)
}


/// Matches a list binding element: anything that's legal in a list unpacking
/// environment.
///
/// There are four cases:
/// - anonymous slurp: `let [...] = x`
/// - named slurp: `let [...y] = x`
/// - singleton binding: `let [y] = x`
/// - singleton binding with default: `let [y = z] = x`
fn list_binding_element<'a>(input: In<'a>) -> Out<'a, Tagged<ListBindingElement>> {
    alt((

        // Named and anonymous slurps
        map(
            tuple((
                ellipsis,
                opt(identifier)
            )),
            |(e, ident)| {
                let loc = if let Some(i) = ident {
                    Span::from(e.span()..i.span())
                } else {
                    e.span()
                };
                ident.map(ListBindingElement::SlurpTo).unwrap_or(ListBindingElement::Slurp).tag(loc)
            },
        ),

        // Singleton bindings with or without defaults
        map(
            tuple((
                binding,
                opt(preceded(
                    eq,
                    fail(expression, SyntaxElement::Expression),
                )),
            )),

            |(b, e)| {
                let span = if let Some(d) = &e {
                    Span::from(b.span()..d.outer())
                } else {
                    b.span()
                };

                ListBindingElement::Binding {
                    binding: b,
                    default: e.map(PExpr::inner)
                }.tag(span)
            },
        ),

    ))(input)
}


/// Matches a list binding.
///
/// This is a comma-separated list of list binding elements, optionally
/// terminated by a comma.
fn list_binding<'a, T, U, V>(
    initializer: impl Parser<'a, Tagged<V>> + Copy,
    terminator: impl Parser<'a, Tagged<V>> + Copy,
    err_terminator_or_item: T,
    err_terminator_or_separator: U,
) -> impl Parser<'a, (Tagged<ListBinding>, V)>
where
    Syntax: From<T> + From<U>,
    T: Copy,
    U: Copy,
{
    move |input| map(
        seplist(
            initializer,
            list_binding_element,
            comma,
            terminator,
            err_terminator_or_item,
            err_terminator_or_separator,
        ),
        |(a, x, b)| (ListBinding(x).tag(a.span()..b.span()), b.unwrap()),
    )(input)
}


/// Matches a map binding element: anything that's legal in a map unpacking environment.
///
/// There are five cases:
/// - named slurp: `let {...y} = x`
/// - singleton binding: `let {y} = x`
/// - singleton binding with unpacking: `let {y as z} = x`
/// - singleton binding with default: `let {y = z} = x`
/// - singleton binding with unpacking and default: `let {y as z = q} = x`
fn map_binding_element<'a>(input: In<'a>) -> Out<'a, Tagged<MapBindingElement>> {
    alt((

        // Slurp
        map(
            tuple((
                ellipsis,
                fail(identifier, SyntaxElement::Identifier),
            )),
            |(e, i)| MapBindingElement::SlurpTo(i).tag(e.span()..i.span()),
        ),

        // All variants of singleton bindings
        map(
            tuple((
                alt((

                    // With unpacking
                    map(
                        tuple((
                            map_identifier,
                            preceded(
                                keyword("as"),
                                fail(binding, SyntaxElement::Binding),
                            ),
                        )),
                        |(name, binding)| (name, Some(binding)),
                    ),

                    // Without unpacking
                    map(
                        identifier,
                        |name| (name, None),
                    ),

                )),

                // Optional default
                opt(
                    preceded(
                        eq,
                        fail(expression, SyntaxElement::Expression),
                    ),
                ),
            )),

            |((name, binding), default)| {
                let mut loc = name.span();
                if let Some(b) = &binding { loc = Span::from(loc..b.span()); };
                if let Some(d) = &default { loc = Span::from(loc..d.outer()); };
                let rval = match binding {
                    None => MapBindingElement::Binding {
                        key: name,
                        binding: Binding::Identifier(name).tag(&name),
                        default: default.map(PExpr::inner),
                    },
                    Some(binding) => MapBindingElement::Binding {
                        key: name,
                        binding,
                        default: default.map(PExpr::inner),
                    },
                };
                rval.tag(loc)
            },
        ),

    ))(input)
}


/// Matches a map binding.
///
/// This is a comma-separated list of list binding elements, optionally
/// terminated by a comma.
fn map_binding<'a, T, U, V>(
    initializer: impl Parser<'a, Tagged<V>> + Copy,
    terminator: impl Parser<'a, Tagged<V>> + Copy,
    err_terminator_or_item: T,
    err_terminator_or_separator: U,
) -> impl FnMut(In<'a>) -> Out<'a, Tagged<MapBinding>>
where
    Syntax: From<T> + From<U>,
    T: Copy,
    U: Copy,
{
    move |input: In<'a>| map(
        seplist(
            initializer,
            map_binding_element,
            comma,
            terminator,
            err_terminator_or_item,
            err_terminator_or_separator,
        ),
        |(a, x, b)| MapBinding(x).tag(a.span()..b.span()),
    )(input)
}


/// Matches a binding.
///
/// There are three cases:
/// - An identifier binding (leaf node)
/// - A list binding
/// - A map binding
fn binding<'a>(input: In<'a>) -> Out<'a, Tagged<Binding>> {
    alt((
        ident_binding,

        // TODO: Do we need double up location tagging here?
        map(
            list_binding(
                |i| open_bracket(i),
                |i| close_bracket(i),
                (TokenType::CloseBracket, SyntaxElement::ListBindingElement),
                (TokenType::CloseBracket, TokenType::Comma),
            ),
            |(x,_)| {
                x.wrap(Binding::List)
                // let loc = x.span();
                // x.wrap(Binding::List, x.loc)
            },
        ),

        // TODO: Do we need double up location tagging here?
        map(
            map_binding(
                |i| open_brace(i),
                |i| close_brace(i),
                (TokenType::CloseBrace, SyntaxElement::MapBindingElement),
                (TokenType::CloseBrace, TokenType::Comma),
            ),
            |x| {
                x.wrap(Binding::Map)
                // let loc = x.span();
                // x.wrap(Binding::Map, loc)
            },
        )
    ))(input)
}


/// Matches a standard function definition.
///
/// This is the 'fn' keyword followed by a list binding and an optional map
/// binding, each with slightly different delimiters from conventional
/// let-binding syntax. It is concluded by a double arrow (=>) and an
/// expression.
fn normal_function<'a>(input: In<'a>) -> Out<'a, PExpr> {
    let (i, (args, end)) = list_binding(
        |i| pipe(i),
        |i| alt((pipe, semicolon))(i),
        (TokenType::Pipe, TokenType::SemiColon, SyntaxElement::PosParam),
        (TokenType::Pipe, TokenType::SemiColon, TokenType::Comma),
    ).parse(input)?;

    // println!("parsing normal function, end is {:?}", end);

    let (j, kwargs) = if end == ";" {
        // println!("keyword args");
        let (j, kwargs) = map_binding(
            |i: In<'a>| { let loc = i.position(); Ok((i, "".tag(loc.with_length(0)))) },
            |i| pipe(i),
            (TokenType::Pipe, SyntaxElement::KeywordParam),
            (TokenType::Pipe, TokenType::Comma),
        )(i)?;
        (j, Some(kwargs))
    } else {
        (i, None)
    };

    let (l, expr) = fail(expression, SyntaxElement::Expression).parse(j)?;
    let span = args.span()..expr.outer();

    let result = PExpr::Naked(Expr::Function {
        positional: args.unwrap(),
        keywords: kwargs.map(Tagged::unwrap),
        expression: expr.inner().to_box(),
    }.tag(span));

    Ok((l, result))
}


/// Matches a keyword-only function.
///
/// This is a conventional map binding followed by a double arrow (=>) and an
/// expression.
fn keyword_function<'a>(input: In<'a>) -> Out<'a, PExpr> {
    map(
        tuple((
            map_binding(
                |i| open_brace_pipe(i),
                |i| close_brace_pipe(i),
                (TokenType::CloseBracePipe, SyntaxElement::KeywordParam),
                (TokenType::CloseBracePipe, TokenType::Comma),
            ),
            fail(expression, SyntaxElement::Expression),
        )),

        |(kwargs, expr)| {
            let span = kwargs.span()..expr.outer();
            PExpr::Naked(Expr::Function {
                positional: ListBinding(vec![]),
                keywords: Some(kwargs.unwrap()),
                expression: Box::new(expr.inner()),
            }.tag(span))
        },
    )(input)
}


/// Matches a function.
///
/// The heavy lifting of this function is done by [`normal_function`] or
/// [`keyword_function`].
fn function<'a>(input: In<'a>) -> Out<'a, PExpr> {
    alt((
        keyword_function,
        normal_function,
    ))(input)
}


/// Matches a let-binding block.
///
/// This is an arbitrary (non-empty) sequence of let-bindings followed by the
/// keyword 'in' and then an expression.
///
/// A let-binding consists of the keyword 'let' followed by a binding, an equals
/// symbol and an expression.
fn let_block<'a>(input: In<'a>) -> Out<'a, PExpr> {
    map(
        tuple((
            // position,
            many1(
                tuple((
                    keyword("let"),
                    fail(binding, SyntaxElement::Binding),
                    preceded(
                        fail(eq, TokenType::Eq),
                        fail(expression, SyntaxElement::Expression),
                    ),
                )),
            ),
            preceded(
                fail(keyword("in"), SyntaxElement::In),
                fail(expression, SyntaxElement::Expression),
            ),
        )),
        |(bindings, expr)| {
            let span = bindings.first().unwrap().0.span()..expr.outer();
            PExpr::Naked(Expr::Let {
                bindings: bindings.into_iter().map(|(_,x,y)| (x,y.inner())).collect(),
                expression: Box::new(expr.inner())
            }.tag(span))
        },
    )(input)
}


/// Matches a branching expression (tertiary operator).
///
/// This consists of the keywords 'if', 'then' and 'else', each followed by an
/// expression.
fn branch<'a>(input: In<'a>) -> Out<'a, PExpr> {
    map(
        tuple((
            keyword("if"),
            fail(expression, SyntaxElement::Expression),
            preceded(
                fail(keyword("then"), SyntaxElement::Then),
                fail(expression, SyntaxElement::Expression),
            ),
            preceded(
                fail(keyword("else"), SyntaxElement::Else),
                fail(expression, SyntaxElement::Expression),
            ),
        )),

        |(start, condition, true_branch, false_branch)| {
            let span = start.span()..false_branch.outer();
            PExpr::Naked(Expr::Branch {
                condition: Box::new(condition.inner()),
                true_branch: Box::new(true_branch.inner()),
                false_branch: Box::new(false_branch.inner()),
            }.tag(span))
        },
    )(input)
}


/// Matches a composite expression.
///
/// This is a catch-all terms for special expressions that do not participate in
/// the operator sequence: let blocks, branches, and functions.
fn composite<'a>(input: In<'a>) -> Out<'a, PExpr> {
    alt((
        let_block,
        branch,
        function,
    ))(input)
}


/// Matches any expression.
fn expression<'a>(input: In<'a>) -> Out<'a, PExpr> {
    alt((
        composite,
        disjunction,
    ))(input)
}


/// Matches an import statement.
///
/// An import statement consists of the keyword 'import' followed by a raw
/// string (no interpolated segments), the keyword 'as' and a binding pattern.
fn import<'a>(input: In<'a>) -> Out<'a, TopLevel> {
    map(
        tuple((
            preceded(
                keyword("import"),
                fail(tuple((
                    double_quote,
                    raw_string,
                    fail(double_quote, TokenType::DoubleQuote),
                )), SyntaxElement::ImportPath),
            ),
            preceded(
                fail(keyword("as"), SyntaxElement::As),
                fail(binding, SyntaxElement::Binding),
            )
        )),
        |((a, path, b), binding)| TopLevel::Import(path.tag(a.span()..b.span()), binding),
    )(input)
}


/// Matches a file.
///
/// A file consists of an arbitrary number of top-level statements followed by a
/// single expression.
fn file<'a>(input: In<'a>) -> Out<'a, File> {
    map(
        tuple((
            many0(import),
            fail(expression, SyntaxElement::Expression),
        )),
        |(statements, expression)| File { statements, expression: expression.inner() },
    )(input)
}


/// Parse the input and return a [`File`] object.
pub fn parse(input: &str) -> Result<File, Error> {
    let cache = Lexer::cache();
    let lexer = Lexer::new(input).with_cache(&cache);
    file(lexer).map_or_else(
        |err| match err {
            NomError::Incomplete(_) => Err(Error::default()),
            NomError::Error(e) | NomError::Failure(e) => Err(e.to_error()),
        },
        |(_, node)| {
            node.validate()?;
            Ok(node)
        }
    )
}
