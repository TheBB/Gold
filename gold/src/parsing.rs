use std::fmt::Debug;
use std::num::{ParseFloatError, ParseIntError};

use num_bigint::BigInt;
use num_bigint::ParseBigIntError;

use nom::{
    branch::alt,
    combinator::{map, map_res, opt, value, verify},
    error::{ContextError, ErrorKind, FromExternalError, ParseError},
    multi::{many0, many1},
    sequence::{delimited, preceded, terminated, tuple},
    Err as NomError, IResult, Parser as NomParser,
};

use crate::ast::high::*;
use crate::error::{Error, Span, Syntax, SyntaxElement, SyntaxError, Tagged, Taggable};
use crate::formatting::{
    AlignSpec, FloatFormatType, FormatSpec, FormatType, GroupingSpec, IntegerFormatType, SignSpec,
    StringAlignSpec, UppercaseSpec,
};
use crate::lexing::{CachedLexResult, CachedLexer, Lexer, TokenType};
use crate::types::{UnOp, BinOp, Key};
use crate::Object;

trait ExplainError {
    fn error<'a, T>(lex: CachedLexer<'a>, reason: T) -> Self
    where
        Syntax: From<T>;
}

impl ExplainError for SyntaxError {
    fn error<'a, T>(lex: CachedLexer<'a>, reason: T) -> Self
    where
        Syntax: From<T>,
    {
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

/// Convert a multiline string from source code to string by removing leading
/// whitespace from each line according to the rules for such strings.
fn multiline(s: &str) -> String {
    let mut lines = s.lines();

    let first = lines.next().unwrap().trim_start();

    let rest: Vec<&str> = lines.filter(|s: &&str| !(*s).trim().is_empty()).collect();
    let indent = rest
        .iter()
        .filter(|s: &&&str| !s.trim().is_empty())
        .map(|s: &&str| {
            (*s).chars()
                .take_while(|c| c.is_whitespace())
                .map(|_| 1)
                .sum()
        })
        .min()
        .unwrap_or(0);

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

    fn map_wrap<F, U>(self, f: F) -> Paren<U>
    where
        F: FnOnce(Tagged<T>) -> U,
    {
        match self {
            Self::Naked(x) => Paren::<U>::Naked(x.wrap(f)),
            Self::Parenthesized(x) => Paren::<U>::Parenthesized(x.map(|y| y.wrap(f))),
        }
    }
}

type PExpr = Paren<Expr>;
type PList = Paren<ListElement>;
type PMap = Paren<MapElement>;

type OpCons = fn(Tagged<Expr>, loc: Span) -> Transform;

type In<'a> = CachedLexer<'a>;
type Out<'a, T> = IResult<In<'a>, T, SyntaxError>;

trait Parser<'a, T>: NomParser<In<'a>, T, SyntaxError> {}
impl<'a, T, P> Parser<'a, T> for P where P: NomParser<In<'a>, T, SyntaxError> {}

/// Parser that always succeeds and consumes nothing
fn success<'a>(input: In<'a>) -> Out<'a, Tagged<&'a str>> {
    let loc = input.position();
    Ok((input, "".tag(loc.with_length(0))))
}

/// Convert errors to failures.
fn fail<'a, O, T>(mut parser: impl Parser<'a, O>, reason: T) -> impl Parser<'a, O>
where
    Syntax: From<T>,
    T: Copy,
{
    move |input: In<'a>| {
        parser.parse(input.clone()).map_err(|err| match err {
            NomError::Failure(e) => NomError::Failure(e),
            NomError::Error(_) => NomError::Failure(SyntaxError::error(input, reason)),
            _ => err,
        })
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
fn do_skip<'a, O>(parser: impl Parser<'a, O>) -> impl Parser<'a, (O, bool)> {
    apply_skip(parser, true)
}

/// Create an item parser that never skips the following separator. See
/// [`seplist_opt_delim`] for details.
fn dont_skip<'a, O>(parser: impl Parser<'a, O>) -> impl Parser<'a, (O, bool)> {
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
            let u = item.parse(i.clone());

            // Try to parse an item
            match u {
                // Parsing item failed: we expect a terminator
                Err(NomError::Error(_)) => match terminator.parse(i.clone()) {
                    Err(NomError::Error(_)) => {
                        return Err(NomError::Failure(SyntaxError::error(
                            i,
                            err_terminator_or_item,
                        )))
                    }
                    Err(e) => return Err(e),
                    Ok((i, termr)) => return Ok((i, (initr, items, termr))),
                },

                // Parsing item failed irrecoverably
                Err(e) => return Err(e),

                // Parsing item succeeded
                Ok((j, (it, skip_separator))) => {
                    i = j;
                    expect_separator = !skip_separator;
                    items.push(it);
                }
            }

            // If at this moment we don't expect a separator, try to parse a terminator
            if !expect_separator {
                match terminator.parse(i.clone()) {
                    Err(NomError::Error(_)) => {}
                    Err(e) => {
                        return Err(e);
                    }
                    Ok((i, termr)) => return Ok((i, (initr, items, termr))),
                }

                continue;
            }

            // Try to parse a separator
            match separator.parse(i.clone()) {
                // Parsing separator failed: we expect a terminator
                Err(NomError::Error(_)) => match terminator.parse(i.clone()) {
                    Err(NomError::Error(_)) => {
                        return Err(NomError::Failure(SyntaxError::error(
                            i,
                            err_terminator_or_separator,
                        )))
                    }
                    Err(e) => return Err(e),
                    Ok((i, termr)) => return Ok((i, (initr, items, termr))),
                },

                // Parsing separator failed irrecoverably
                Err(e) => return Err(e),

                // Parsing separator succeeded
                Ok((j, _)) => {
                    i = j;
                }
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
    seplist_opt_delim(
        initializer,
        item_parser,
        separator,
        terminator,
        err_terminator_or_item,
        err_terminator_or_separator,
    )
}

/// Wrap the output of a parser in Paren::Naked.
fn naked<'a, U>(parser: impl Parser<'a, Tagged<U>>) -> impl Parser<'a, Paren<U>> {
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

tok! {name, Name}
tok! {float, Float}
tok! {integer, Integer}

tok! {asterisk, Asterisk}
tok! {caret, Caret}
tok! {close_brace, CloseBrace}
tok! {close_brace_pipe, CloseBracePipe}
tok! {close_bracket, CloseBracket}
tok! {close_paren, CloseParen}
tok! {colon, Colon}
tok! {comma, Comma}
tok! {dot, Dot}
tok! {double_eq, DoubleEq}
tok! {double_quote, DoubleQuote}
tok! {double_slash, DoubleSlash}
tok! {ellipsis, Ellipsis}
tok! {eq, Eq}
tok! {exclam_eq, ExclamEq}
tok! {greater_eq, GreaterEq}
tok! {greater, Greater}
tok! {less_eq, LessEq}
tok! {less, Less}
tok! {minus, Minus}
tok! {open_brace, OpenBrace}
tok! {open_brace_pipe, OpenBracePipe}
tok! {open_bracket, OpenBracket}
tok! {open_paren, OpenParen}
tok! {pipe, Pipe}
tok! {plus, Plus}
tok! {semicolon, SemiColon}
tok! {slash, Slash}

tok! {map_name, Name, next_key}
tok! {map_colon, Colon, next_key}
tok! {map_dollar, Dollar, next_key}
tok! {map_double_colon, DoubleColon, next_key}
tok! {map_ellipsis, Ellipsis, next_key}

tok! {string_lit, StringLit, next_string}
tok! {string_dollar, Dollar, next_string}
tok! {string_double_quote, DoubleQuote, next_string}

tok! {fmtspec_char_raw, Char, next_fmtspec}
tok! {fmtspec_number_raw, Integer, next_fmtspec}

/// Match a single multiline string starting at a column.
fn multistring<'a>(col: u32) -> impl Parser<'a, Tagged<&'a str>> {
    move |lex: In<'a>| {
        lex.next_multistring(col)
            .map(|(lex, tok)| (lex, tok.as_ref().text.tag(&tok)))
            .map_err(NomError::Error)
    }
}

/// Match a single named keyword. This does not match if the keyword is a prefix
/// of some other name or identifier.
fn keyword_raw<'a>(
    parser: impl Parser<'a, Tagged<&'a str>>,
    value: &'a str,
) -> impl Parser<'a, Tagged<&'a str>> {
    verify(parser, move |out| *out.as_ref() == value)
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
static KEYWORDS: [&'static str; 17] = [
    "for", "when", "if", "then", "else", "let", "in", "has", "true", "false", "null", "and", "or",
    "not", "as", "import", "fn",
];

/// Match an identfier.
///
/// This parser will refuse to match known keywords (see [`KEYWORDS`]).
fn identifier<'a>(input: In<'a>) -> Out<'a, Tagged<Key>> {
    map(
        verify(name, |out| !KEYWORDS.contains(out.as_ref())),
        |span| span.map(Key::new),
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
    naked(alt((
        map_res(float, |span| {
            span.as_ref()
                .replace('_', "")
                .parse::<f64>()
                .map(|x| Expr::Literal(Object::from(x)).tag(&span))
        }),
        map_res(integer, |span| {
            let text = span.as_ref().replace('_', "");
            let y = text
                .parse::<i64>()
                .map(Object::from)
                .or_else(|_| text.parse::<BigInt>().map(Object::from))
                .map(Expr::Literal);
            y.map(|x| x.tag(&span))
        }),
    )))
    .parse(input)
}

/// Matches a raw string part.
///
/// This means all characters up to a terminating symbol: either a closing quote
/// or a dollar sign, signifying the beginning of an interpolated segment. This
/// parser does *not* parse the initial quote or the terminating symbol,
/// whatever that may be.
fn raw_string<'a>(input: In<'a>) -> Out<'a, String> {
    map(string_lit, |span| {
        let mut out = "".to_string();
        let mut chars = span.as_ref().char_indices();
        loop {
            match chars.next() {
                Some((_, '\\')) => match chars.next() {
                    Some((_, '\\')) => {
                        out += "\\";
                    }
                    Some((_, '"')) => {
                        out += "\"";
                    }
                    Some((_, '$')) => {
                        out += "$";
                    }
                    Some((_, _)) => {
                        // TODO: Calculate accurate error
                        continue;
                    }
                    None => {
                        // TODO: Calculate accurate error
                        break;
                    }
                },
                Some((_, c)) => out.push(c),
                None => {
                    break;
                }
            }
        }

        out
    })(input)
}

/// Matches a non-interpolated string element.
///
/// This is just the output of [`raw_string`] returned as a [`StringElement`].
fn string_data<'a>(input: In<'a>) -> Out<'a, StringElement> {
    map(raw_string, StringElement::raw)(input)
}

/// Matches a specific format specifier character.
fn fmtspec_char<'a>(c: char) -> impl Parser<'a, ()> {
    value(
        (),
        verify(fmtspec_char_raw, move |out| {
            out.unwrap().chars().next() == Some(c)
        }),
    )
}

/// Matches a format specifier number.
fn fmtspec_number<'a>(input: In<'a>) -> Out<'a, usize> {
    map_res(fmtspec_number_raw, |out| out.as_ref().parse::<usize>())(input)
}

/// Matches a format specifier alignment.
fn fmtspec_align<'a>(input: In<'a>) -> Out<'a, AlignSpec> {
    alt((
        value(AlignSpec::String(StringAlignSpec::Left), fmtspec_char('<')),
        value(AlignSpec::String(StringAlignSpec::Right), fmtspec_char('>')),
        value(
            AlignSpec::String(StringAlignSpec::Center),
            fmtspec_char('^'),
        ),
        value(AlignSpec::AfterSign, fmtspec_char('=')),
    ))(input)
}

/// Matches a format specifier fill and alignment.
fn fmtspec_fill_align<'a>(input: In<'a>) -> Out<'a, (Option<char>, AlignSpec)> {
    alt((
        map(tuple((fmtspec_char_raw, fmtspec_align)), |(fill, align)| {
            (Some(fill.unwrap().chars().next().unwrap()), align)
        }),
        map(fmtspec_align, |align| (None, align)),
    ))(input)
}

/// Matches a format specifier sign
fn fmtspec_sign<'a>(input: In<'a>) -> Out<'a, SignSpec> {
    alt((
        value(SignSpec::Plus, fmtspec_char('+')),
        value(SignSpec::Minus, fmtspec_char('-')),
        value(SignSpec::Space, fmtspec_char(' ')),
    ))(input)
}

/// Matches a format specifier grouping
fn fmtspec_grouping<'a>(input: In<'a>) -> Out<'a, GroupingSpec> {
    alt((
        value(GroupingSpec::Comma, fmtspec_char(',')),
        value(GroupingSpec::Underscore, fmtspec_char('_')),
    ))(input)
}

/// Matches a format speficier type
fn fmtspec_type<'a>(input: In<'a>) -> Out<'a, FormatType> {
    alt((
        value(FormatType::String, fmtspec_char('s')),
        value(
            FormatType::Integer(IntegerFormatType::Binary),
            fmtspec_char('b'),
        ),
        value(
            FormatType::Integer(IntegerFormatType::Character),
            fmtspec_char('c'),
        ),
        value(
            FormatType::Integer(IntegerFormatType::Decimal),
            fmtspec_char('d'),
        ),
        value(
            FormatType::Integer(IntegerFormatType::Octal),
            fmtspec_char('o'),
        ),
        value(
            FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Lower)),
            fmtspec_char('x'),
        ),
        value(
            FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Upper)),
            fmtspec_char('X'),
        ),
        value(
            FormatType::Float(FloatFormatType::Sci(UppercaseSpec::Lower)),
            fmtspec_char('e'),
        ),
        value(
            FormatType::Float(FloatFormatType::Sci(UppercaseSpec::Upper)),
            fmtspec_char('E'),
        ),
        value(FormatType::Float(FloatFormatType::Fixed), fmtspec_char('f')),
        value(
            FormatType::Float(FloatFormatType::General),
            fmtspec_char('g'),
        ),
        value(
            FormatType::Float(FloatFormatType::Percentage),
            fmtspec_char('%'),
        ),
    ))(input)
}

/// Matches a format specifier
fn format_specifier<'a>(input: In<'a>) -> Out<'a, FormatSpec> {
    map(
        tuple((
            opt(fmtspec_fill_align),
            opt(fmtspec_sign),
            opt(value(true, fmtspec_char('#'))),
            opt(value(true, fmtspec_char('0'))),
            opt(fmtspec_number),
            opt(fmtspec_grouping),
            opt(preceded(fmtspec_char('.'), fmtspec_number)),
            opt(fmtspec_type),
        )),
        |(fill_align, sign, alternate, zero_in, width, grouping, precision, fmt_type)| {
            let zero = zero_in.unwrap_or_default();
            FormatSpec {
                fill: match fill_align {
                    None => {
                        if zero {
                            '0'
                        } else {
                            ' '
                        }
                    }
                    Some((None, _)) => ' ',
                    Some((Some(fill), _)) => fill,
                },

                align: match (fill_align, zero) {
                    (Some((_, align)), _) => Some(align), //fill_align.map(|(_, align)| align)
                    (None, true) => Some(AlignSpec::AfterSign),
                    _ => None,
                },

                alternate: alternate.unwrap_or_default(),

                sign,
                width,
                grouping,
                precision,
                fmt_type,
            }
        },
    )(input)
}

/// Matches an interpolated string element.
fn string_interp<'a>(input: In<'a>) -> Out<'a, StringElement> {
    map(
        delimited(
            terminated(string_dollar, fail(open_brace, TokenType::OpenBrace)),
            tuple((
                fail(expression, SyntaxElement::Expression),
                opt(preceded(colon, format_specifier)),
            )),
            fail(close_brace, TokenType::CloseBrace),
        ),
        |(expression, fmt_spec)| StringElement::Interpolate(expression.inner(), fmt_spec),
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
        |(a, x, b)| x.tag(a.span()..b.span()),
    )(input)
}

/// Matches a string.
///
/// This consists of a sequence of one or more string parts, separated by
/// whitespace.
fn string<'a>(input: In<'a>) -> Out<'a, PExpr> {
    naked(map(many1(string_part), |x| {
        let start = x.first().unwrap().span();
        let end = x.last().unwrap().span();
        let elements: Vec<StringElement> = x.into_iter().map(Tagged::unwrap).flatten().collect();
        Expr::string(elements).tag(start..end)
    }))
    .parse(input)
}

/// Matches a boolean literal.
fn boolean<'a>(input: In<'a>) -> Out<'a, PExpr> {
    naked(alt((
        map(keyword("false"), |tok| {
            Expr::Literal(Object::from(false)).tag(&tok)
        }),
        map(keyword("true"), |tok| {
            Expr::Literal(Object::from(true)).tag(&tok)
        }),
    )))
    .parse(input)
}

/// Matches a null literal.
fn null<'a>(input: In<'a>) -> Out<'a, PExpr> {
    naked(map(keyword("null"), |tok| {
        Expr::Literal(Object::null()).tag(&tok)
    }))
    .parse(input)
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
        naked(map(identifier, |x| x.wrap(Expr::Identifier))),
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
            tuple((ellipsis, fail(expression, SyntaxElement::Expression))),
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
                    fail(list_element, SyntaxElement::ListElement),
                ),
            )),
            |(start, binding, iterable, expr)| {
                let span = start.span()..expr.outer();
                ListElement::Loop {
                    binding,
                    iterable: iterable.inner(),
                    element: Box::new(expr.inner()),
                }
                .tag(span)
            },
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
                }
                .tag(span)
            },
        )),
        // Singleton
        map(expression, |x| x.map_wrap(ListElement::Singleton)),
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
    ))
    .parse(input)
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
                tuple((map_dollar, fail(expression, SyntaxElement::Expression))),
                |(d, ex)| {
                    let span = d.span()..ex.outer();
                    PExpr::Parenthesized(ex.inner().tag(span))
                },
            ),
            string,
            naked(map(map_identifier, |key| {
                key.map(Object::from).map(Expr::Literal)
            })),
        )),
    ))(input)
}

/// Matches a singleton value in a map context.
///
/// This is either a double colon followed by a multiline string, or a single
/// comma followed by an expression.
fn map_value_singleton<'a>(col: u32, input: In<'a>) -> Out<'a, (PExpr, bool)> {
    alt((
        do_skip(naked(map(
            preceded(map_double_colon, multistring(col)),
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
    let ret = MapElement::Singleton {
        key: key.inner(),
        value: value.inner(),
    }
    .tag(span);

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
            tuple((map_ellipsis, fail(expression, SyntaxElement::Expression))),
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
                }
                .tag(span);
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
                    element: Box::new(expr.inner()),
                }
                .tag(span);
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
    ))
    .parse(input)
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
        |(start, expr, end)| PExpr::Parenthesized(expr.inner().tag(start.span()..end.span())),
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
fn object_access<'a>(input: In<'a>) -> Out<'a, Tagged<Transform>> {
    map(
        tuple((dot, fail(identifier, SyntaxElement::Identifier))),
        |(dot, out)| {
            Transform::BinOp(
                BinOp::Index.tag(&dot),
                Box::new(out.map(Object::from).map(Expr::Literal)),
            )
            .tag(dot.span()..out.span())
        },
    )(input)
}

/// Matches a bracket-syntax subscripting operator.
///
/// This is an open bracket followed by any expression and a closing bracket.
fn object_index<'a>(input: In<'a>) -> Out<'a, Tagged<Transform>> {
    map(
        tuple((
            open_bracket,
            fail(expression, SyntaxElement::Expression),
            fail(close_bracket, TokenType::CloseBracket),
        )),
        |(a, expr, b)| {
            let span = Span::from(a.span()..b.span());
            Transform::BinOp(BinOp::Index.tag(span), Box::new(expr.inner())).tag(span)
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
            tuple((ellipsis, fail(expression, SyntaxElement::Expression))),
            |(x, y)| {
                let span = x.span()..y.outer();
                ArgElement::Splat(y.inner()).tag(span)
            },
        ),
        // Keyword
        map(
            tuple((
                identifier,
                preceded(colon, fail(expression, SyntaxElement::Expression)),
            )),
            |(name, expr)| {
                let span = name.span()..expr.outer();
                ArgElement::Keyword(name, expr.inner()).tag(span)
            },
        ),
        // Singleton
        map(expression, |x| {
            let span = x.outer();
            ArgElement::Singleton(x.inner()).tag(span)
        }),
    ))(input)
}

/// Matches a function call operator.
///
/// This is an open parenthesis followed by a possibly empty list of
/// comma-separated argument elements, followed by an optional comma and a
/// closin parenthesis.
fn function_call<'a>(input: In<'a>) -> Out<'a, Tagged<Transform>> {
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
            Transform::FunCall(expr.tag(span)).tag(span)
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
            many0(alt((object_access, object_index, function_call))),
        )),
        |(expr, ops)| {
            ops.into_iter().fold(expr, |expr, operator| {
                let span = expr.outer()..operator.span();
                PExpr::Naked(
                    Expr::Transformed {
                        operand: Box::new(expr.inner()),
                        transform: operator.unwrap(),
                    }
                    .tag(span),
                )
            })
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
                ops.into_iter().rev().fold(expr, |expr, operator| {
                    let span = operator.span()..expr.outer();
                    PExpr::Naked(
                        Expr::Transformed {
                            operand: Box::new(expr.inner()),
                            transform: Transform::UnOp(operator),
                        }
                        .tag(span),
                    )
                })
            },
        ),
    ))(input)
}

/// Utility parser for parsing a single binary operator with operand,
/// collectively termed a 'transform'.
///
/// * `transformer` - a parser whose result is, loosely, a function
///   `Expr -> Transform`.
/// * `operand` - a parser whose result is an `Expr`.
///
/// The result is the output of `transformer` applied to the output of
/// `operand`, which is a `Transform`.
fn binop<'a>(
    transformer: impl Parser<'a, Tagged<OpCons>>,
    operand: impl Parser<'a, PExpr>,
) -> impl Parser<'a, Tagged<Transform>> {
    map(
        tuple((transformer, fail(operand, SyntaxElement::Operand))),
        |(func, expr)| {
            let span = func.span()..expr.outer();
            func.as_ref()(expr.inner(), func.span()).tag(span)
        },
    )
}

/// Utility parser for parsing a left- or right-associative sequence of
/// operators.
///
/// * `transform` - a parser returning a `Transform`, normally created with
///   `binop`.
/// * `operand` -  a parser returning an expression to be acted upon by the
///   transform
/// * `right` - true if right-associative, false if left-associative.
fn binops<'a>(
    transform: impl Parser<'a, Tagged<Transform>>,
    operand: impl Parser<'a, PExpr>,
    right: bool,
) -> impl Parser<'a, PExpr> {
    map(tuple((operand, many0(transform))), move |(expr, ops)| {
        let acc = |expr: PExpr, operator: Tagged<Transform>| {
            let span = expr.outer()..operator.span();
            PExpr::Naked(
                Expr::Transformed {
                    operand: Box::new(expr.inner()),
                    transform: operator.unwrap(),
                }
                .tag(span),
            )
        };
        if right {
            ops.into_iter().rev().fold(expr, acc)
        } else {
            ops.into_iter().fold(expr, acc)
        }
    })
}

/// Matches the exponentiation precedence level.
///
/// The exponentiation operator, unlike practically every other operator, is
/// right-associative, and asymmetric in its operands: it binds tighter than
/// prefix operators on the left, but not on the right.
fn power<'a>(input: In<'a>) -> Out<'a, PExpr> {
    binops(
        binop(
            alt((map(caret, |x| (Transform::power as OpCons).tag(&x)),)),
            prefixed,
        ),
        postfixed,
        true,
    )
    .parse(input)
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
            map(asterisk, |x| (Transform::multiply as OpCons).tag(&x)),
            map(double_slash, |x| {
                (Transform::integer_divide as OpCons).tag(&x)
            }),
            map(slash, |x| (Transform::divide as OpCons).tag(&x)),
        )),
        prefixed,
    )
    .parse(input)
}

/// Matches the addition predecence level.
fn sum<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((
            map(plus, |x| (Transform::add as OpCons).tag(&x)),
            map(minus, |x| (Transform::subtract as OpCons).tag(&x)),
        )),
        product,
    )
    .parse(input)
}

/// Matches the inequality comparison precedence level.
fn inequality<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((
            map(less_eq, |x| (Transform::less_equal as OpCons).tag(&x)),
            map(less, |x| (Transform::less as OpCons).tag(&x)),
            map(greater_eq, |x| (Transform::greater_equal as OpCons).tag(&x)),
            map(greater, |x| (Transform::greater as OpCons).tag(&x)),
        )),
        sum,
    )
    .parse(input)
}

/// Matches the equality comparison precedence level.
fn equality<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((
            map(double_eq, |x| (Transform::equal as OpCons).tag(&x)),
            map(exclam_eq, |x| (Transform::not_equal as OpCons).tag(&x)),
        )),
        inequality,
    )
    .parse(input)
}

/// Matches the contains precedence level.
fn contains<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((map(keyword("has"), |x| {
            (Transform::contains as OpCons).tag(&x)
        }),)),
        equality,
    )
    .parse(input)
}

/// Matches the conjunction ('and') precedence level.
fn conjunction<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((map(keyword("and"), |x| (Transform::and as OpCons).tag(&x)),)),
        contains,
    )
    .parse(input)
}

/// Matches the disjunction ('or') precedence level.
fn disjunction<'a>(input: In<'a>) -> Out<'a, PExpr> {
    lbinop(
        alt((map(keyword("or"), |x| (Transform::or as OpCons).tag(&x)),)),
        conjunction,
    )
    .parse(input)
}

/// Matches an identifier binding. This is essentially the same as a normal
/// identifier.
fn ident_binding<'a>(input: In<'a>) -> Out<'a, Tagged<Binding>> {
    alt((map(identifier, |out| Binding::Identifier(out).tag(&out)),))(input)
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
        map(tuple((ellipsis, opt(identifier))), |(e, ident)| {
            let loc = if let Some(i) = ident {
                Span::from(e.span()..i.span())
            } else {
                e.span()
            };
            ident
                .map(ListBindingElement::SlurpTo)
                .unwrap_or(ListBindingElement::Slurp)
                .tag(loc)
        }),
        // Singleton bindings with or without defaults
        map(
            tuple((
                binding,
                opt(preceded(eq, fail(expression, SyntaxElement::Expression))),
            )),
            |(b, e)| {
                let span = if let Some(d) = &e {
                    Span::from(b.span()..d.outer())
                } else {
                    b.span()
                };

                ListBindingElement::Binding {
                    binding: b,
                    default: e.map(PExpr::inner),
                }
                .tag(span)
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
) -> impl Parser<'a, (Tagged<ListBinding>, Tagged<V>)>
where
    Syntax: From<T> + From<U>,
    T: Copy,
    U: Copy,
{
    move |input| {
        map(
            seplist(
                initializer,
                list_binding_element,
                comma,
                terminator,
                err_terminator_or_item,
                err_terminator_or_separator,
            ),
            |(a, x, b)| (ListBinding::new(x).tag(a.span()..b.span()), b),
        )(input)
    }
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
            tuple((ellipsis, fail(identifier, SyntaxElement::Identifier))),
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
                            preceded(keyword("as"), fail(binding, SyntaxElement::Binding)),
                        )),
                        |(name, binding)| (name, Some(binding)),
                    ),
                    // Without unpacking
                    map(identifier, |name| (name, None)),
                )),
                // Optional default
                opt(preceded(eq, fail(expression, SyntaxElement::Expression))),
            )),
            |((name, binding), default)| {
                let mut loc = name.span();
                if let Some(b) = &binding {
                    loc = Span::from(loc..b.span());
                };
                if let Some(d) = &default {
                    loc = Span::from(loc..d.outer());
                };
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
    move |input: In<'a>| {
        map(
            seplist(
                initializer,
                map_binding_element,
                comma,
                terminator,
                err_terminator_or_item,
                err_terminator_or_separator,
            ),
            |(a, x, b)| MapBinding::new(x).tag(a.span()..b.span()),
        )(input)
    }
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
            |(x, _)| x.wrap(Binding::List),
        ),
        // TODO: Do we need double up location tagging here?
        map(
            map_binding(
                |i| open_brace(i),
                |i| close_brace(i),
                (TokenType::CloseBrace, SyntaxElement::MapBindingElement),
                (TokenType::CloseBrace, TokenType::Comma),
            ),
            |x| x.wrap(Binding::Map),
        ),
    ))(input)
}

/// Matches a function definition.
///
/// This is the 'fn' keyword followed by either an open paren or brace.
///
/// An open paren must be followed by a list binding and optionally a semicolon
/// and a map binding, then a close paren and an expression.
///
/// An open brace must be followed by a map binding, a close brace and an
/// expression.
fn function_new_style<'a>(input: In<'a>) -> Out<'a, PExpr> {
    let (i, init) = keyword("fn").parse(input)?;
    let (i, opener) = fail(
        alt((open_paren, open_brace)),
        (TokenType::OpenParen, TokenType::OpenBrace),
    )
    .parse(i)?;

    let (i, args, kwargs, expr) = if opener.unwrap() == "(" {
        // Parse a normal function
        let (i, (args, end)) = list_binding(
            success,
            |i| alt((close_paren, semicolon))(i),
            (
                TokenType::CloseParen,
                TokenType::SemiColon,
                SyntaxElement::PosParam,
            ),
            (
                TokenType::CloseParen,
                TokenType::SemiColon,
                TokenType::Comma,
            ),
        )
        .parse(i)?;

        let (i, kwargs) = if *end.as_ref() == ";" {
            let (i, kwargs) = map_binding(
                success,
                |i| close_paren(i),
                (TokenType::CloseParen, SyntaxElement::KeywordParam),
                (TokenType::CloseParen, TokenType::Comma),
            )
            .parse(i)?;

            let span = end.span()..kwargs.span();
            (i, Some(kwargs.retag(span)))
        } else {
            (i, None)
        };

        let (i, expr) = fail(expression, SyntaxElement::Expression).parse(i)?;

        let span = opener.span()..args.span();
        (i, args.retag(span), kwargs, expr)
    } else {
        // Parse a keyword function
        let (i, kwargs) = map_binding(
            success,
            |i| close_brace(i),
            (TokenType::CloseBrace, SyntaxElement::KeywordParam),
            (TokenType::CloseBrace, TokenType::Comma),
        )
        .parse(i)?;
        let (i, expr) = fail(expression, SyntaxElement::Expression).parse(i)?;

        let span = opener.span()..kwargs.span();
        let kwargs = kwargs.retag(span);
        (
            i,
            ListBinding::new(vec![]).tag(kwargs.span().with_length(1)),
            Some(kwargs),
            expr,
        )
    };

    let span = init.span()..expr.outer();
    let result = PExpr::Naked(
        Expr::Function {
            positional: args,
            keywords: kwargs,
            expression: Box::new(expr.inner()),
        }
        .tag(span),
    );

    Ok((i, result))
}

/// Matches a standard function definition.
///
/// This is the 'fn' keyword followed by a list binding and an optional map
/// binding, each with slightly different delimiters from conventional
/// let-binding syntax. It is concluded by a double arrow (=>) and an
/// expression.
fn normal_function_old_style<'a>(input: In<'a>) -> Out<'a, PExpr> {
    let (i, (args, end)) = list_binding(
        |i| pipe(i),
        |i| alt((pipe, semicolon))(i),
        (
            TokenType::Pipe,
            TokenType::SemiColon,
            SyntaxElement::PosParam,
        ),
        (TokenType::Pipe, TokenType::SemiColon, TokenType::Comma),
    )
    .parse(input)?;

    let (j, kwargs) = if *end.as_ref() == ";" {
        let (j, kwargs) = map_binding(
            success,
            // |i: In<'a>| { let loc = i.position(); Ok((i, "".tag(loc.with_length(0)))) },
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

    let result = PExpr::Naked(
        Expr::Function {
            positional: args,
            keywords: kwargs,
            expression: Box::new(expr.inner()),
        }
        .tag(span),
    );

    eprintln!("gold: |...| syntax is deprecated, use fn (...) instead");
    Ok((l, result))
}

/// Matches a keyword-only function.
///
/// This is a conventional map binding followed by a double arrow (=>) and an
/// expression.
fn keyword_function_old_style<'a>(input: In<'a>) -> Out<'a, PExpr> {
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
            eprintln!("gold: {{|...|}} syntax is deprecated, use fn {{...}} instead");
            PExpr::Naked(
                Expr::Function {
                    positional: ListBinding::new(vec![]).tag(kwargs.span().with_length(1)),
                    keywords: Some(kwargs),
                    expression: Box::new(expr.inner()),
                }
                .tag(span),
            )
        },
    )(input)
}

/// Matches a function.
///
/// The heavy lifting of this function is done by [`normal_function`] or
/// [`keyword_function`].
fn function<'a>(input: In<'a>) -> Out<'a, PExpr> {
    alt((
        function_new_style,
        keyword_function_old_style,
        normal_function_old_style,
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
            many1(tuple((
                keyword("let"),
                fail(binding, SyntaxElement::Binding),
                preceded(
                    fail(eq, TokenType::Eq),
                    fail(expression, SyntaxElement::Expression),
                ),
            ))),
            preceded(
                fail(keyword("in"), SyntaxElement::In),
                fail(expression, SyntaxElement::Expression),
            ),
        )),
        |(bindings, expr)| {
            let span = bindings.first().unwrap().0.span()..expr.outer();
            PExpr::Naked(
                Expr::Let {
                    bindings: bindings
                        .into_iter()
                        .map(|(_, x, y)| (x, y.inner()))
                        .collect(),
                    expression: Box::new(expr.inner()),
                }
                .tag(span),
            )
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
            PExpr::Naked(
                Expr::Branch {
                    condition: Box::new(condition.inner()),
                    true_branch: Box::new(true_branch.inner()),
                    false_branch: Box::new(false_branch.inner()),
                }
                .tag(span),
            )
        },
    )(input)
}

/// Matches a composite expression.
///
/// This is a catch-all terms for special expressions that do not participate in
/// the operator sequence: let blocks, branches, and functions.
fn composite<'a>(input: In<'a>) -> Out<'a, PExpr> {
    alt((let_block, branch, function))(input)
}

/// Matches any expression.
fn expression<'a>(input: In<'a>) -> Out<'a, PExpr> {
    alt((composite, disjunction))(input)
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
                fail(
                    tuple((
                        double_quote,
                        raw_string,
                        fail(double_quote, TokenType::DoubleQuote),
                    )),
                    SyntaxElement::ImportPath,
                ),
            ),
            preceded(
                fail(keyword("as"), SyntaxElement::As),
                fail(binding, SyntaxElement::Binding),
            ),
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
        tuple((many0(import), fail(expression, SyntaxElement::Expression))),
        |(statements, expression)| File {
            statements,
            expression: expression.inner(),
        },
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
            Ok(node)
        },
    )
}

#[cfg(test)]
mod tests {
    use crate::{Object, Error};
    use crate::ast::high::*;
    use crate::error::{Tagged, Taggable, Span, Action, Syntax, SyntaxElement as S};
    use crate::formatting::{FormatSpec, AlignSpec, FormatType, GroupingSpec, SignSpec, StringAlignSpec};
    use crate::lexing::TokenType as T;
    use crate::types::Key;
    use super::parse as parse_file;

    trait ToExpr {
        fn expr<T>(self, loc: T) -> Tagged<Expr>
        where
            Span: From<T>;
    }

    impl<U> ToExpr for U
    where
        Object: From<U>,
    {
        fn expr<T>(self, loc: T) -> Tagged<Expr>
        where
            Span: From<T>,
        {
            Expr::Literal(Object::from(self)).tag(loc)
        }
    }

    trait ToKey {
        fn key<T>(self, loc: T) -> Tagged<Key>
        where
            Span: From<T>;
    }

    impl<U> ToKey for U
    where
        U: AsRef<str>,
    {
        fn key<T>(self, loc: T) -> Tagged<Key>
        where
            Span: From<T>,
        {
            Key::new(self).tag(loc)
        }
    }

    trait ToIdentifier {
        fn id<T>(self, loc: T) -> Tagged<Expr>
        where
            Span: From<T>;
    }

    impl<U> ToIdentifier for U
    where
        U: ToKey,
    {
        fn id<T>(self, loc: T) -> Tagged<Expr>
        where
            Span: From<T>,
        {
            self.key(loc).wrap(Expr::Identifier)
        }
    }

    trait ToBindingIdentifier {
        fn bid<T>(self, loc: T) -> Tagged<Binding>
        where
            Span: From<T>,
            T: Copy;
    }

    impl<U> ToBindingIdentifier for U
    where
        U: ToKey,
    {
        fn bid<T>(self, loc: T) -> Tagged<Binding>
        where
            Span: From<T>,
            T: Copy,
        {
            Binding::Identifier(self.key(loc)).tag(loc)
        }
    }

    trait ToListElement {
        fn lel<T>(self, loc: T) -> Tagged<ListElement>
        where
            Span: From<T>;
    }

    impl<U> ToListElement for U
    where
        Object: From<U>,
    {
        fn lel<T>(self, loc: T) -> Tagged<ListElement>
        where
            Span: From<T>,
        {
            Expr::Literal(Object::from(self))
                .tag(loc)
                .wrap(ListElement::Singleton)
        }
    }

    trait ToMapElement {
        fn mel(self) -> Tagged<MapElement>;
    }

    impl ToMapElement for (Tagged<Expr>, Tagged<Expr>) {
        fn mel(self) -> Tagged<MapElement> {
            let loc = Span::from(self.0.span()..self.1.span());
            MapElement::Singleton {
                key: self.0,
                value: self.1,
            }
            .tag(loc)
        }
    }

    trait ToBox<T>
    where
        T: Sized,
    {
        /// Convert self to a boxed value.
        fn to_box(self) -> Box<T>;
    }

    impl<T> ToBox<T> for T {
        fn to_box(self) -> Box<T> {
            Box::new(self)
        }
    }

    trait ToLiteralKey {
        fn lit<T>(self, loc: T) -> Tagged<Expr>
        where
            Span: From<T>;
    }

    impl<U> ToLiteralKey for U
    where
        U: ToKey,
    {
        fn lit<T>(self, loc: T) -> Tagged<Expr>
        where
            Span: From<T>,
        {
            self.key(loc).map(Object::from).map(Expr::Literal)
        }
    }

    fn expr(input: &str) -> Result<Tagged<Expr>, Error> {
        parse_file(input)
            .map(|x| x.expression)
            .map_err(Error::unrender)
    }

    #[test]
    fn booleans_and_null() {
        assert_eq!(expr("true"), Ok(true.expr(0..4)));
        assert_eq!(expr("false"), Ok(false.expr(0..5)));
        assert_eq!(expr("null"), Ok(Object::null().expr(0..4)));
    }

    #[test]
    fn integers() {
        assert_eq!(expr("0"), Ok(0.expr(0)));
        assert_eq!(expr("1"), Ok(1.expr(0)));
        assert_eq!(expr("1  "), Ok(1.expr(0)));
        assert_eq!(
            expr("9223372036854775807"),
            Ok(9223372036854775807i64.expr(0..19))
        );
        assert_eq!(
            expr("9223372036854776000"),
            Ok(Object::new_int_from_str("9223372036854776000").unwrap().expr(0..19))
        );
    }

    #[test]
    fn floats() {
        assert_eq!(expr("0.0"), Ok(0f64.expr(0..3)));
        assert_eq!(expr("0."), Ok(0f64.expr(0..2)));
        assert_eq!(expr(".0"), Ok(0f64.expr(0..2)));
        assert_eq!(expr("0e0"), Ok(0f64.expr(0..3)));
        assert_eq!(expr("0e1"), Ok(0f64.expr(0..3)));
        assert_eq!(expr("1."), Ok(1f64.expr(0..2)));
        assert_eq!(expr("1e+1"), Ok(10f64.expr(0..4)));
        assert_eq!(expr("1e1"), Ok(10f64.expr(0..3)));
        assert_eq!(expr("1e-1"), Ok(0.1f64.expr(0..4)));
    }

    #[test]
    fn strings() {
        assert_eq!(expr("\"\""), Ok("".expr(0..2)));
        assert_eq!(expr("\"dingbob\""), Ok("dingbob".expr(0..9)));
        assert_eq!(expr("\"ding\\\"bob\""), Ok("ding\"bob".expr(0..11)));
        assert_eq!(expr("\"ding\\\\bob\""), Ok("ding\\bob".expr(0..11)));

        assert_eq!(
            expr("\"dingbob${a}\""),
            Ok(Expr::String(vec![
                StringElement::raw("dingbob"),
                StringElement::Interpolate("a".id(10), None),
            ])
            .tag(0..13)),
        );

        assert_eq!(
            expr("\"dingbob${ a}\""),
            Ok(Expr::String(vec![
                StringElement::raw("dingbob"),
                StringElement::Interpolate("a".id(11), None),
            ])
            .tag(0..14)),
        );

        assert_eq!(
            expr("\"alpha\" \"bravo\""),
            Ok(Expr::String(vec![
                StringElement::raw("alpha"),
                StringElement::raw("bravo"),
            ])
            .tag(0..15))
        );
    }

    #[test]
    fn string_format() {
        assert_eq!(
            FormatSpec::default(),
            FormatSpec {
                fill: ' ',
                align: None,
                sign: None,
                alternate: false,
                width: None,
                grouping: None,
                precision: None,
                fmt_type: None,
            }
        );

        assert_eq!(
            expr("\"${a}\""),
            Ok(Expr::String(vec![StringElement::Interpolate("a".id(3), None),]).tag(0..6))
        );

        assert_eq!(
            expr("\"${a:}\""),
            Ok(Expr::String(vec![StringElement::Interpolate(
                "a".id(3),
                Some(Default::default()),
            ),])
            .tag(0..7))
        );

        assert_eq!(
            expr("\"${a: >+30}\""),
            Ok(Expr::String(vec![StringElement::Interpolate(
                "a".id(3),
                Some(FormatSpec {
                    align: Some(AlignSpec::String(StringAlignSpec::Right)),
                    sign: Some(SignSpec::Plus),
                    width: Some(30),
                    ..Default::default()
                })
            ),])
            .tag(0..12))
        );

        assert_eq!(
            expr("\"${a:$^#.3}\""),
            Ok(Expr::String(vec![StringElement::Interpolate(
                "a".id(3),
                Some(FormatSpec {
                    fill: '$',
                    align: Some(AlignSpec::String(StringAlignSpec::Center)),
                    alternate: true,
                    precision: Some(3),
                    ..Default::default()
                })
            ),])
            .tag(0..12))
        );

        assert_eq!(
            expr("\"${a:0,.5s}\""),
            Ok(Expr::String(vec![StringElement::Interpolate(
                "a".id(3),
                Some(FormatSpec {
                    fill: '0',
                    align: Some(AlignSpec::AfterSign),
                    grouping: Some(GroupingSpec::Comma),
                    precision: Some(5),
                    fmt_type: Some(FormatType::String),
                    ..Default::default()
                })
            ),])
            .tag(0..12))
        );
    }

    #[test]
    fn identifiers() {
        assert_eq!(expr("dingbob"), Ok("dingbob".id(0..7)));
        assert_eq!(expr("lets"), Ok("lets".id(0..4)));
        assert_eq!(expr("not1"), Ok("not1".id(0..4)));
    }

    #[test]
    fn lists() {
        assert_eq!(expr("[]"), Ok(Expr::List(vec![]).tag(0..2)),);

        assert_eq!(expr("[   ]"), Ok(Expr::List(vec![]).tag(0..5)),);

        assert_eq!(
            expr("[true]"),
            Ok(Expr::List(vec![true.lel(1..5),]).tag(0..6)),
        );

        assert_eq!(
            expr("[\"\"]"),
            Ok(Expr::List(vec!["".lel(1..3),]).tag(0..4)),
        );

        assert_eq!(expr("[1,]"), Ok(Expr::List(vec![1.lel(1),]).tag(0..4)),);

        assert_eq!(
            expr("[  1   ,  ]"),
            Ok(Expr::List(vec![1.lel(3),]).tag(0..11)),
        );

        assert_eq!(
            expr("[  1   ,2  ]"),
            Ok(Expr::List(vec![1.lel(3), 2.lel(8),]).tag(0..12)),
        );

        assert_eq!(
            expr("[  1   ,2  ,]"),
            Ok(Expr::List(vec![1.lel(3), 2.lel(8),]).tag(0..13)),
        );

        assert_eq!(
            expr("[1, false, 2.3, \"fable\", lel]"),
            Ok(Expr::List(vec![
                1.lel(1),
                false.lel(4..9),
                2.3.lel(11..14),
                "fable".lel(16..23),
                ListElement::Singleton("lel".id(25..28)).tag(25..28),
            ])
            .tag(0..29)),
        );

        assert_eq!(
            expr("[1, ...x, y]"),
            Ok(Expr::List(vec![
                1.lel(1),
                "x".id(7).wrap(ListElement::Splat).retag(4..8),
                "y".id(10).wrap(ListElement::Singleton),
            ])
            .tag(0..12)),
        );

        assert_eq!(
            expr("[1, for x in y: x, 2]"),
            Ok(Expr::List(vec![
                1.lel(1),
                ListElement::Loop {
                    binding: "x".bid(8),
                    iterable: "y".id(13),
                    element: "x".id(16).wrap(ListElement::Singleton).to_box(),
                }
                .tag(4..17),
                2.lel(19),
            ])
            .tag(0..21)),
        );

        assert_eq!(
            expr("[when f(x): x]"),
            Ok(Expr::List(vec![ListElement::Cond {
                condition: "f"
                    .id(6)
                    .funcall(vec!["x".id(8).wrap(ArgElement::Singleton),], 7..10)
                    .tag(6..10),
                element: "x".id(12).wrap(ListElement::Singleton).to_box(),
            }
            .tag(1..13),])
            .tag(0..14)),
        );

        assert_eq!(
            expr("[ 1 , ... x , when x : y , for x in y : z , ]"),
            Ok(Expr::List(vec![
                1.lel(2),
                "x".id(10).wrap(ListElement::Splat).retag(6..11),
                ListElement::Cond {
                    condition: "x".id(19),
                    element: "y".id(23).wrap(ListElement::Singleton).to_box(),
                }
                .tag(14..24),
                ListElement::Loop {
                    binding: "x".bid(31),
                    iterable: "y".id(36),
                    element: "z".id(40).wrap(ListElement::Singleton).to_box(),
                }
                .tag(27..41),
            ])
            .tag(0..45)),
        );

        assert_eq!(
            expr("[ (1) , ... (x), when x: (y) , for x in y: (z) ]"),
            Ok(Expr::List(vec![
                1.lel(3),
                "x".id(13).wrap(ListElement::Splat).retag(8..15),
                ListElement::Cond {
                    condition: "x".id(22),
                    element: "y".id(26).wrap(ListElement::Singleton).to_box(),
                }
                .tag(17..28),
                ListElement::Loop {
                    binding: "x".bid(35),
                    iterable: "y".id(40),
                    element: "z".id(44).wrap(ListElement::Singleton).to_box(),
                }
                .tag(31..46),
            ])
            .tag(0..48)),
        );
    }

    #[test]
    fn nested_lists() {
        assert_eq!(
            expr("[[]]"),
            Ok(Expr::List(vec![Expr::List(vec![]).tag(1..3).wrap(ListElement::Singleton),]).tag(0..4)),
        );

        assert_eq!(
            expr("[1, [2]]"),
            Ok(Expr::List(vec![
                1.lel(1),
                Expr::List(vec![2.lel(5),])
                    .tag(4..7)
                    .wrap(ListElement::Singleton),
            ])
            .tag(0..8)),
        );
    }

    #[test]
    fn maps() {
        assert_eq!(expr("{}"), Ok(Expr::Map(vec![]).tag(0..2)),);

        assert_eq!(expr("{  }"), Ok(Expr::Map(vec![]).tag(0..4)),);

        assert_eq!(
            expr("{a: 1}"),
            Ok(Expr::Map(vec![("a".lit(1), 1.expr(4)).mel(),]).tag(0..6)),
        );

        assert_eq!(
            expr("{a: 1,}"),
            Ok(Expr::Map(vec![("a".lit(1), 1.expr(4)).mel(),]).tag(0..7)),
        );

        assert_eq!(
            expr("{  a :1,}"),
            Ok(Expr::Map(vec![("a".lit(3), 1.expr(6)).mel(),]).tag(0..9)),
        );

        assert_eq!(
            expr("{a: 1  ,b:2}"),
            Ok(Expr::Map(vec![
                ("a".lit(1), 1.expr(4)).mel(),
                ("b".lit(8), 2.expr(10)).mel(),
            ])
            .tag(0..12)),
        );

        assert_eq!(
            expr("{che9: false}"),
            Ok(Expr::Map(vec![("che9".lit(1..5), false.expr(7..12)).mel(),]).tag(0..13)),
        );

        assert_eq!(
            expr("{fable: \"fable\"}"),
            Ok(Expr::Map(vec![("fable".lit(1..6), "fable".expr(8..15)).mel(),]).tag(0..16)),
        );

        assert_eq!(
            expr("{format: 1}"),
            Ok(Expr::Map(vec![("format".lit(1..7), 1.expr(9)).mel(),]).tag(0..11)),
        );

        assert_eq!(
            expr("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: 1e1}"),
            Ok(Expr::Map(vec![
                ("a".lit(1), 1.expr(4)).mel(),
                ("b".lit(7), true.expr(10..14)).mel(),
                ("c".lit(16), 20.0.expr(19..23)).mel(),
                ("d".lit(25), "hoho".expr(28..34)).mel(),
                ("e".lit(36), 10.0.expr(39..42)).mel(),
            ])
            .tag(0..43)),
        );

        assert_eq!(
            expr("{ident-with-hyphen: 1}"),
            Ok(Expr::Map(vec![("ident-with-hyphen".lit(1..18), 1.expr(20)).mel(),]).tag(0..22)),
        );

        assert_eq!(
            expr("{$z: y}"),
            Ok(Expr::Map(vec![MapElement::Singleton {
                key: "z".id(2),
                value: "y".id(5)
            }
            .tag(1..6),])
            .tag(0..7)),
        );

        assert_eq!(
            expr("{$(z): y}"),
            Ok(Expr::Map(vec![MapElement::Singleton {
                key: "z".id(3),
                value: "y".id(7),
            }
            .tag(1..8),])
            .tag(0..9)),
        );

        assert_eq!(
            expr("{\"z\": y}"),
            Ok(Expr::Map(vec![("z".lit(1..4), "y".id(6)).mel(),]).tag(0..8)),
        );

        assert_eq!(
            expr(concat!("{\n", "   z:: here's some text\n", "}\n",)),
            Ok(Expr::Map(vec![(
                "z".lit(5).with_coord(1, 3),
                "here's some text".expr(8..26).with_coord(1, 6)
            )
                .mel(),])
            .tag(0..27)),
        );

        assert_eq!(
            expr(concat!(
                "{\n",
                "   z:: here's some\n",
                "       text\n",
                "}\n",
            )),
            Ok(Expr::Map(vec![(
                "z".lit(5).with_coord(1, 3),
                "here's some\ntext".expr(8..33).with_coord(1, 6)
            )
                .mel(),])
            .tag(0..34)),
        );

        assert_eq!(
            expr(concat!("{\n", "   z:: here's some\n", "     text\n", "}\n",)),
            Ok(Expr::Map(vec![(
                "z".lit(5).with_coord(1, 3),
                "here's some\ntext".expr(8..31).with_coord(1, 6)
            )
                .mel(),])
            .tag(0..32)),
        );

        assert_eq!(
            expr(concat!(
                "{\n",
                "   z::\n",
                "     here's some\n",
                "     text\n",
                "}\n",
            )),
            Ok(Expr::Map(vec![(
                "z".lit(5).with_coord(1, 3),
                "here's some\ntext".expr(8..36).with_coord(1, 6)
            )
                .mel(),])
            .tag(0..37)),
        );

        assert_eq!(
            expr(concat!(
                "{\n",
                "   z::\n",
                "     here's some\n",
                "       text\n",
                "}\n",
            )),
            Ok(Expr::Map(vec![(
                "z".lit(5).with_coord(1, 3),
                "here's some\n  text".expr(8..38).with_coord(1, 6)
            )
                .mel(),])
            .tag(0..39)),
        );

        assert_eq!(
            expr(concat!(
                "{\n",
                "   z::\n",
                "       here's some\n",
                "     text\n",
                "}\n",
            )),
            Ok(Expr::Map(vec![(
                "z".lit(5).with_coord(1, 3),
                "  here's some\ntext".expr(8..38).with_coord(1, 6)
            )
                .mel(),])
            .tag(0..39)),
        );

        assert_eq!(
            expr(concat!("{\n", "    a:: x\n", "    b: y,\n", "}\n",)),
            Ok(Expr::Map(vec![
                (
                    "a".lit(6).with_coord(1, 4),
                    "x".expr(9..12).with_coord(1, 7)
                )
                    .mel(),
                (
                    "b".lit(16).with_coord(2, 4),
                    "y".key(19).with_coord(2, 7).wrap(Expr::Identifier)
                )
                    .mel(),
            ])
            .tag(0..23)),
        );

        assert_eq!(
            expr("{...y, x: 1}"),
            Ok(Expr::Map(vec![
                MapElement::Splat("y".id(4)).tag(1..5),
                ("x".lit(7), 1.expr(10)).mel(),
            ])
            .tag(0..12)),
        );

        assert_eq!(
            expr("{for [x,y] in z: x: y}"),
            Ok(Expr::Map(vec![MapElement::Loop {
                binding: Binding::List(
                    ListBinding::new(vec![
                        ListBindingElement::Binding {
                            binding: "x".bid(6),
                            default: None
                        }
                        .tag(6),
                        ListBindingElement::Binding {
                            binding: "y".bid(8),
                            default: None
                        }
                        .tag(8),
                    ])
                    .tag(5..10)
                )
                .tag(5..10),
                iterable: "z".id(14),
                element: ("x".lit(17), "y".id(20)).mel().to_box(),
            }
            .tag(1..21),])
            .tag(0..22)),
        );

        assert_eq!(
            expr("{when f(x): z: y}"),
            Ok(Expr::Map(vec![MapElement::Cond {
                condition: "f"
                    .id(6)
                    .funcall(vec![ArgElement::Singleton("x".id(8)).tag(8),], 7..10)
                    .tag(6..10),
                element: ("z".lit(12), "y".id(15)).mel().to_box(),
            }
            .tag(1..16),])
            .tag(0..17)),
        );

        assert_eq!(
            expr("{ a : 1 , ... x , when x : b : y , for x in y : c : z , $ f : 2 , }"),
            Ok(Expr::Map(vec![
                ("a".lit(2), 1.expr(6)).mel(),
                MapElement::Splat("x".id(14)).tag(10..15),
                MapElement::Cond {
                    condition: "x".id(23),
                    element: ("b".lit(27), "y".id(31)).mel().to_box(),
                }
                .tag(18..32),
                MapElement::Loop {
                    binding: "x".bid(39),
                    iterable: "y".id(44),
                    element: ("c".lit(48), "z".id(52)).mel().to_box(),
                }
                .tag(35..53),
                MapElement::Singleton {
                    key: "f".id(58),
                    value: 2.expr(62)
                }
                .tag(56..63),
            ])
            .tag(0..67)),
        );

        assert_eq!(
            expr("{ a : (1), ... (x), when x : b : (y), for x in y : c : (z), $ f : (2) }"),
            Ok(Expr::Map(vec![
                MapElement::Singleton {
                    key: "a".lit(2),
                    value: 1.expr(7)
                }
                .tag(2..9),
                MapElement::Splat("x".id(16)).tag(11..18),
                MapElement::Cond {
                    condition: "x".id(25),
                    element: MapElement::Singleton {
                        key: "b".lit(29),
                        value: "y".id(34)
                    }
                    .tag(29..36)
                    .to_box(),
                }
                .tag(20..36),
                MapElement::Loop {
                    binding: "x".bid(42),
                    iterable: "y".id(47),
                    element: MapElement::Singleton {
                        key: "c".lit(51),
                        value: "z".id(56)
                    }
                    .tag(51..58)
                    .to_box(),
                }
                .tag(38..58),
                MapElement::Singleton {
                    key: "f".id(62),
                    value: 2.expr(67)
                }
                .tag(60..69),
            ])
            .tag(0..71)),
        );
    }

    #[test]
    fn let_blocks() {
        assert_eq!(
            expr("let a = \"b\" in 1"),
            Ok(Expr::Let {
                bindings: vec![("a".bid(4), "b".expr(8..11)),],
                expression: 1.expr(15).to_box(),
            }
            .tag(0..16)),
        );

        assert_eq!(
            expr("let a = 1 let b = 2 in a"),
            Ok(Expr::Let {
                bindings: vec![("a".bid(4), 1.expr(8)), ("b".bid(14), 2.expr(18)),],
                expression: "a".id(23).to_box(),
            }
            .tag(0..24)),
        );

        assert_eq!(
            expr("let [a, b=1, ...] = c in [a, b]"),
            Ok(Expr::Let {
                bindings: vec![(
                    Binding::List(
                        ListBinding::new(vec![
                            ListBindingElement::Binding {
                                binding: "a".bid(5),
                                default: None
                            }
                            .tag(5),
                            ListBindingElement::Binding {
                                binding: "b".bid(8),
                                default: Some(1.expr(10))
                            }
                            .tag(8..11),
                            ListBindingElement::Slurp.tag(13..16),
                        ])
                        .tag(4..17)
                    )
                    .tag(4..17),
                    "c".id(20),
                ),],
                expression: Box::new(
                    Expr::List(vec![
                        "a".id(26).wrap(ListElement::Singleton),
                        "b".id(29).wrap(ListElement::Singleton),
                    ])
                    .tag(25..31)
                ),
            }
            .tag(0..31)),
        );

        assert_eq!(
            expr("let [_, ...rest] = list in rest"),
            Ok(Expr::Let {
                bindings: vec![(
                    Binding::List(
                        ListBinding::new(vec![
                            ListBindingElement::Binding {
                                binding: "_".bid(5),
                                default: None
                            }
                            .tag(5),
                            ListBindingElement::SlurpTo("rest".key(11..15)).tag(8..15),
                        ])
                        .tag(4..16)
                    )
                    .tag(4..16),
                    "list".id(19..23),
                ),],
                expression: "rest".id(27..31).to_box(),
            }
            .tag(0..31)),
        );

        assert_eq!(
            expr("let [...a] = b in a"),
            Ok(Expr::Let {
                bindings: vec![(
                    Binding::List(
                        ListBinding::new(vec![ListBindingElement::SlurpTo("a".key(8)).tag(5..9),])
                            .tag(4..10)
                    )
                    .tag(4..10),
                    "b".id(13),
                ),],
                expression: "a".id(18).to_box(),
            }
            .tag(0..19)),
        );

        assert_eq!(
            expr("let [...a,] = b in a"),
            Ok(Expr::Let {
                bindings: vec![(
                    Binding::List(
                        ListBinding::new(vec![ListBindingElement::SlurpTo("a".key(8)).tag(5..9),])
                            .tag(4..11)
                    )
                    .tag(4..11),
                    "b".id(14),
                ),],
                expression: "a".id(19).to_box(),
            }
            .tag(0..20)),
        );

        assert_eq!(
            expr("let {a} = x in a"),
            Ok(Expr::Let {
                bindings: vec![(
                    Binding::Map(
                        MapBinding::new(vec![MapBindingElement::Binding {
                            key: "a".key(5),
                            binding: "a".bid(5),
                            default: None,
                        }
                        .tag(5),])
                        .tag(4..7)
                    )
                    .tag(4..7),
                    "x".id(10),
                ),],
                expression: "a".id(15).to_box(),
            }
            .tag(0..16)),
        );

        assert_eq!(
            expr("let {a as b} = x in a"),
            Ok(Expr::Let {
                bindings: vec![(
                    Binding::Map(
                        MapBinding::new(vec![MapBindingElement::Binding {
                            key: "a".key(5),
                            binding: "b".bid(10),
                            default: None,
                        }
                        .tag(5..11),])
                        .tag(4..12)
                    )
                    .tag(4..12),
                    "x".id(15),
                ),],
                expression: "a".id(20).to_box(),
            }
            .tag(0..21)),
        );

        assert_eq!(
            expr("let {a = y} = x in a"),
            Ok(Expr::Let {
                bindings: vec![(
                    Binding::Map(
                        MapBinding::new(vec![MapBindingElement::Binding {
                            key: "a".key(5),
                            binding: "a".bid(5),
                            default: Some("y".id(9)),
                        }
                        .tag(5..10),])
                        .tag(4..11)
                    )
                    .tag(4..11),
                    "x".id(14),
                ),],
                expression: "a".id(19).to_box(),
            }
            .tag(0..20)),
        );

        assert_eq!(
            expr("let {a as b = y} = x in a"),
            Ok(Expr::Let {
                bindings: vec![(
                    Binding::Map(
                        MapBinding::new(vec![MapBindingElement::Binding {
                            key: "a".key(5),
                            binding: "b".bid(10),
                            default: Some("y".id(14)),
                        }
                        .tag(5..15),])
                        .tag(4..16)
                    )
                    .tag(4..16),
                    "x".id(19),
                ),],
                expression: "a".id(24).to_box(),
            }
            .tag(0..25)),
        );

        assert_eq!(
            expr("let [ y = (1) ] = x in y"),
            Ok(Expr::Let {
                bindings: vec![(
                    Binding::List(
                        ListBinding::new(vec![ListBindingElement::Binding {
                            binding: "y".bid(6),
                            default: Some(1.expr(11)),
                        }
                        .tag(6..13),])
                        .tag(4..15)
                    )
                    .tag(4..15),
                    "x".id(18),
                ),],
                expression: "y".id(23).to_box(),
            }
            .tag(0..24))
        );

        assert_eq!(
            expr("let { y = (1) } = x in y"),
            Ok(Expr::Let {
                bindings: vec![(
                    Binding::Map(
                        MapBinding::new(vec![MapBindingElement::Binding {
                            key: "y".key(6),
                            binding: "y".bid(6),
                            default: Some(1.expr(11)),
                        }
                        .tag(6..13),])
                        .tag(4..15)
                    )
                    .tag(4..15),
                    "x".id(18),
                ),],
                expression: "y".id(23).to_box(),
            }
            .tag(0..24))
        );
    }

    #[test]
    fn branching() {
        assert_eq!(
            expr("if a then b else c"),
            Ok(Expr::Branch {
                condition: "a".id(3).to_box(),
                true_branch: "b".id(10).to_box(),
                false_branch: "c".id(17).to_box(),
            }
            .tag(0..18)),
        );
    }

    #[test]
    fn indexing() {
        assert_eq! {
            expr("a.b"),
            Ok(
                "a".id(0)
                .index("b".lit(2), 1).tag(0..3)
            ),
        };

        assert_eq!(
            expr("a[b]"),
            Ok("a".id(0).index("b".id(2), 1..4).tag(0..4)),
        );

        assert_eq!(
            expr("a.b.c"),
            Ok("a"
                .id(0)
                .index("b".lit(2), 1)
                .tag(0..3)
                .index("c".lit(4), 3)
                .tag(0..5)),
        );

        assert_eq!(
            expr("a[b].c"),
            Ok("a"
                .id(0)
                .index("b".id(2), 1..4)
                .tag(0..4)
                .index("c".lit(5), 4)
                .tag(0..6)),
        );

        assert_eq!(
            expr("a.b[c]"),
            Ok("a"
                .id(0)
                .index("b".lit(2), 1)
                .tag(0..3)
                .index("c".id(4), 3..6)
                .tag(0..6)),
        );

        assert_eq!(
            expr("a[b][c]"),
            Ok("a"
                .id(0)
                .index("b".id(2), 1..4)
                .tag(0..4)
                .index("c".id(5), 4..7)
                .tag(0..7)),
        );
    }

    #[test]
    fn funcall() {
        assert_eq!(
            expr("func(1, 2, 3,)"),
            Ok("func"
                .id(0..4)
                .funcall(
                    vec![
                        1.expr(5).wrap(ArgElement::Singleton),
                        2.expr(8).wrap(ArgElement::Singleton),
                        3.expr(11).wrap(ArgElement::Singleton),
                    ],
                    4..14
                )
                .tag(0..14)),
        );

        assert_eq!(
            expr("func(1, 2, a: 3)"),
            Ok("func"
                .id(0..4)
                .funcall(
                    vec![
                        1.expr(5).wrap(ArgElement::Singleton),
                        2.expr(8).wrap(ArgElement::Singleton),
                        ArgElement::Keyword("a".key(11), 3.expr(14),).tag(11..15),
                    ],
                    4..16
                )
                .tag(0..16)),
        );

        assert_eq!(
            expr("func(a: 2, b: 3)"),
            Ok("func"
                .id(0..4)
                .funcall(
                    vec![
                        ArgElement::Keyword("a".key(5), 2.expr(8),).tag(5..9),
                        ArgElement::Keyword("b".key(11), 3.expr(14),).tag(11..15),
                    ],
                    4..16
                )
                .tag(0..16)),
        );

        assert_eq!(
            expr("(fn (x,y) x+y)(1,2)"),
            Ok(Expr::Function {
                positional: ListBinding::new(vec![
                    ListBindingElement::Binding {
                        binding: "x".bid(5),
                        default: None
                    }
                    .tag(5),
                    ListBindingElement::Binding {
                        binding: "y".bid(7),
                        default: None
                    }
                    .tag(7),
                ])
                .tag(4..9),
                keywords: None,
                expression: "x".id(10).add("y".id(12), 11).tag(10..13).to_box(),
            }
            .tag(1..13)
            .funcall(
                vec![
                    1.expr(15).wrap(ArgElement::Singleton),
                    2.expr(17).wrap(ArgElement::Singleton),
                ],
                14..19
            )
            .tag(0..19)),
        );

        assert_eq!(
            expr("func(1, ...y, z: 2, ...q)"),
            Ok("func"
                .id(0..4)
                .funcall(
                    vec![
                        1.expr(5).wrap(ArgElement::Singleton),
                        ArgElement::Splat("y".id(11)).tag(8..12),
                        ArgElement::Keyword("z".key(14), 2.expr(17),).tag(14..18),
                        ArgElement::Splat("q".id(23)).tag(20..24),
                    ],
                    4..25
                )
                .tag(0..25)),
        );
    }

    #[test]
    fn unary_operators() {
        assert_eq!(expr("-1"), Ok(1.expr(1).neg(0).tag(0..2)),);

        assert_eq!(
            expr("- not 1"),
            Ok(1.expr(6).not(2..5).tag(2..7).neg(0).tag(0..7)),
        );

        assert_eq!(
            expr("not -1"),
            Ok(1.expr(5).neg(4).tag(4..6).not(0..3).tag(0..6)),
        );
    }

    #[test]
    fn power_operators() {
        assert_eq!(expr("2^3"), Ok(2.expr(0).pow(3.expr(2), 1).tag(0..3)),);

        assert_eq!(
            expr("2^-3"),
            Ok(2.expr(0).pow(3.expr(3).neg(2).tag(2..4), 1,).tag(0..4)),
        );

        assert_eq!(
            expr("-2^3"),
            Ok(2.expr(1).pow(3.expr(3), 2).tag(1..4).neg(0).tag(0..4)),
        );

        assert_eq!(
            expr("-2^-3"),
            Ok(2.expr(1)
                .pow(3.expr(4).neg(3).tag(3..5), 2..3,)
                .tag(1..5)
                .neg(0)
                .tag(0..5)),
        );
    }

    #[test]
    fn operators() {
        assert_eq!(expr("1 + 2"), Ok(1.expr(0).add(2.expr(4), 2).tag(0..5)),);

        assert_eq!(
            expr("1 / 2 + 3"),
            Ok(1.expr(0)
                .div(2.expr(4), 2)
                .tag(0..5)
                .add(3.expr(8), 6)
                .tag(0..9)),
        );

        assert_eq!(
            expr("1 + 2 - 3 * 4 // 5 / 6"),
            Ok(1.expr(0)
                .add(2.expr(4), 2)
                .tag(0..5)
                .sub(
                    3.expr(8)
                        .mul(4.expr(12), 10)
                        .tag(8..13)
                        .idiv(5.expr(17), 14..16)
                        .tag(8..18)
                        .div(6.expr(21), 19)
                        .tag(8..22),
                    6,
                )
                .tag(0..22)),
        );

        assert_eq!(expr("1 < 2"), Ok(1.expr(0).lt(2.expr(4), 2).tag(0..5)),);

        assert_eq!(
            expr("1 > 2 <= 3 >= 4 == 5 != 6"),
            Ok(1.expr(0)
                .gt(2.expr(4), 2)
                .tag(0..5)
                .lte(3.expr(9), 6..8)
                .tag(0..10)
                .gte(4.expr(14), 11..13)
                .tag(0..15)
                .equal(5.expr(19), 16..18)
                .tag(0..20)
                .not_equal(6.expr(24), 21..23)
                .tag(0..25)),
        );

        assert_eq!(
            expr("1 and 2 or 3"),
            Ok(1.expr(0)
                .and(2.expr(6), 2..5)
                .tag(0..7)
                .or(3.expr(11), 8..10)
                .tag(0..12)),
        );

        assert_eq!(
            expr("2 // 2 * 2"),
            Ok(2.expr(0)
                .idiv(2.expr(5), 2..4)
                .tag(0..6)
                .mul(2.expr(9), 7..8)
                .tag(0..10)),
        );

        assert_eq!(
            expr("2 ^ 2 ^ 2"),
            Ok(2.expr(0)
                .pow(2.expr(4).pow(2.expr(8), 6).tag(4..9), 2,)
                .tag(0..9)),
        );

        assert_eq!(
            expr("-2 ^ 2 ^ 2"),
            Ok(2.expr(1)
                .pow(2.expr(5).pow(2.expr(9), 7).tag(5..10), 3,)
                .tag(1..10)
                .neg(0)
                .tag(0..10)),
        );

        assert_eq!(
            expr("(1 + 2) * 5"),
            Ok(1.expr(1)
                .add(2.expr(5), 3)
                .tag(1..6)
                .mul(5.expr(10), 8)
                .tag(0..11)),
        );
    }

    #[test]
    fn functions() {
        assert_eq!(
            expr("fn () 1"),
            Ok(Expr::Function {
                positional: ListBinding::new(vec![]).tag(3..5),
                keywords: None,
                expression: 1.expr(6).to_box(),
            }
            .tag(0..7)),
        );

        assert_eq!(
            expr("fn (;) 1"),
            Ok(Expr::Function {
                positional: ListBinding::new(vec![]).tag(3..5),
                keywords: Some(MapBinding::new(vec![]).tag(4..6)),
                expression: 1.expr(7).to_box(),
            }
            .tag(0..8)),
        );

        assert_eq!(
            expr("fn {} 1"),
            Ok(Expr::Function {
                positional: ListBinding::new(vec![]).tag(3..4),
                keywords: Some(MapBinding::new(vec![]).tag(3..5)),
                expression: 1.expr(6).to_box(),
            }
            .tag(0..7)),
        );

        assert_eq!(
            expr("fn (a) let b = a in b"),
            Ok(Expr::Function {
                positional: ListBinding::new(vec![ListBindingElement::Binding {
                    binding: "a".bid(4),
                    default: None
                }
                .tag(4),])
                .tag(3..6),
                keywords: None,
                expression: Box::new(
                    Expr::Let {
                        bindings: vec![("b".bid(11), "a".id(15),),],
                        expression: "b".id(20).to_box(),
                    }
                    .tag(7..21)
                ),
            }
            .tag(0..21)),
        );

        assert_eq!(
            expr("fn {x=1, y=2} x + y"),
            Ok(Expr::Function {
                positional: ListBinding::new(vec![]).tag(3..4),
                keywords: Some(
                    MapBinding::new(vec![
                        MapBindingElement::Binding {
                            key: "x".key(4),
                            binding: "x".bid(4),
                            default: Some(1.expr(6)),
                        }
                        .tag(4..7),
                        MapBindingElement::Binding {
                            key: "y".key(9),
                            binding: "y".bid(9),
                            default: Some(2.expr(11)),
                        }
                        .tag(9..12),
                    ])
                    .tag(3..13)
                ),
                expression: "x".id(14).add("y".id(18), 16).tag(14..19).to_box(),
            }
            .tag(0..19)),
        );
    }

    macro_rules! err {
        ($code:expr, $offset:expr, $elt:expr $(,$elts:expr)*) => {
            assert_eq!(
                expr($code),
                Err(Error::new(Syntax::from(($elt $(,$elts)*))).with_locations_vec(vec![(Span::from($offset..$offset), Action::Parse)])),
            )
        };
    }

    // macro_rules! errl {
    //     ($code:expr, $offset:expr, $elt:expr) => {
    //         assert_eq!(
    //             parse($code).map(|x| x.lower()),
    //             Err(Error::new(Reason::Syntax($elt))
    //                 .with_locations_vec(vec![(Span::from($offset), Action::Parse)]))
    //         )
    //     };
    // }

    #[test]
    fn errors() {
        err!("let", 3, S::Binding);
        err!("let a", 5, T::Eq);
        err!("let a =", 7, S::Expression);
        err!("let a = 1", 9, S::In);
        err!("let a = 1 in", 12, S::Expression);

        err!("if", 2, S::Expression);
        err!("if true", 7, S::Then);
        err!("if true then", 12, S::Expression);
        err!("if true then 1", 14, S::Else);
        err!("if true then 1 else", 19, S::Expression);

        err!("[", 1, T::CloseBracket, S::ListElement);
        err!("[1", 2, T::CloseBracket, T::Comma);
        err!("[1,", 3, T::CloseBracket, S::ListElement);
        err!("[...", 4, S::Expression);
        err!("[when", 5, S::Expression);
        err!("[when x", 7, T::Colon);
        err!("[when x:", 8, S::ListElement);
        err!("[when x: 1", 10, T::CloseBracket, T::Comma);
        err!("[for", 4, S::Binding);
        err!("[for x", 6, S::In);
        err!("[for x in", 9, S::Expression);
        err!("[for x in y", 11, T::Colon);
        err!("[for x in y:", 12, S::ListElement);
        err!("[for x in y: z", 14, T::CloseBracket, T::Comma);

        err!("{", 1, T::CloseBrace, S::MapElement);
        err!("{x", 2, T::Colon);
        err!("{x:", 3, S::Expression);
        err!("{x: y", 5, T::CloseBrace, T::Comma);
        err!("{x: y,", 6, T::CloseBrace, S::MapElement);
        err!("{$", 2, S::Expression);
        err!("{$x", 3, T::Colon);
        err!("{$x:", 4, S::Expression);
        err!("{$x: y", 6, T::CloseBrace, T::Comma);
        err!("{$x: y,", 7, T::CloseBrace, S::MapElement);
        err!("{...", 4, S::Expression);
        err!("{when", 5, S::Expression);
        err!("{when x", 7, T::Colon);
        err!("{when x:", 8, S::MapElement);
        err!("{when x: y", 10, T::Colon);
        err!("{when x: y:", 11, S::Expression);
        err!("{when x: y: 1", 13, T::CloseBrace, T::Comma);
        err!("{for", 4, S::Binding);
        err!("{for x", 6, S::In);
        err!("{for x in", 9, S::Expression);
        err!("{for x in y", 11, T::Colon);
        err!("{for x in y:", 12, S::MapElement);
        err!("{for x in y: z", 14, T::Colon);
        err!("{for x in y: z:", 15, S::Expression);
        err!("{for x in y: z: v", 17, T::CloseBrace, T::Comma);

        err!("let", 3, S::Binding);
        err!("let [", 5, T::CloseBracket, S::ListBindingElement);
        err!("let [x", 6, T::CloseBracket, T::Comma);
        err!("let [x,", 7, T::CloseBracket, S::ListBindingElement);
        err!("let [x =", 8, S::Expression);
        err!("let [x = 1", 10, T::CloseBracket, T::Comma);
        err!("let [...", 8, T::CloseBracket, T::Comma);
        err!("let {", 5, T::CloseBrace, S::MapBindingElement);

        err!("let {y", 6, T::CloseBrace, T::Comma);
        err!("let {y,", 7, T::CloseBrace, S::MapBindingElement);
        err!("let {y =", 8, S::Expression);
        err!("let {y = 1", 10, T::CloseBrace, T::Comma);
        err!("let {y as", 9, S::Binding);
        err!("let {y as x =", 13, S::Expression);
        err!("let {...", 8, S::Identifier);
        err!("let {...x", 9, T::CloseBrace, T::Comma);

        err!("(", 1, S::Expression);
        err!("(1", 2, T::CloseParen);

        err!("fn (", 4, T::CloseParen, T::SemiColon, S::PosParam);
        err!("fn (x", 5, T::CloseParen, T::SemiColon, T::Comma);
        err!("fn (x,", 6, T::CloseParen, T::SemiColon, S::PosParam);
        err!("fn (;", 5, T::CloseParen, S::KeywordParam);
        err!("fn (;y", 6, T::CloseParen, T::Comma);
        err!("fn (;y,", 7, T::CloseParen, S::KeywordParam);
        err!("fn ()", 5, S::Expression);
        err!("fn {", 4, T::CloseBrace, S::KeywordParam);
        err!("fn {x", 5, T::CloseBrace, T::Comma);
        err!("fn {x,", 6, T::CloseBrace, S::KeywordParam);
        err!("fn {}", 5, S::Expression);

        err!("\"alpha", 6, T::DoubleQuote);
        err!("\"alpha$", 7, T::OpenBrace);
        err!("\"alpha${", 8, S::Expression);
        err!("\"alpha${1", 9, T::CloseBrace);
        err!("\"alpha${1}", 10, T::DoubleQuote);

        err!("a.", 2, S::Identifier);
        err!("a[", 2, S::Expression);
        err!("a[1", 3, T::CloseBracket);
        err!("a(", 2, T::CloseParen, S::ArgElement);
        err!("a(1", 3, T::CloseParen, T::Comma);
        err!("a(1,", 4, T::CloseParen, S::ArgElement);
        err!("a(x:", 4, S::Expression);
        err!("a(...", 5, S::Expression);

        err!("-", 1, S::Operand);
        err!("1+", 2, S::Operand);

        err!("import", 6, S::ImportPath);
        err!("import \"path\"", 13, S::As);
        err!("import \"path\" as", 16, S::Binding);
        err!("import \"path\" as y", 18, S::Expression);

        // errl!("let [x, ..., y, ...] = z in 2", 16..19, Syntax::MultiSlurp);
        // errl!(
        //     "let {x, ...a, y, ...b} = z in 2",
        //     17..21,
        //     Syntax::MultiSlurp
        // );
    }
}
