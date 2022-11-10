use std::num::{ParseFloatError, ParseIntError};
use std::str::FromStr;

use num_bigint::{BigInt, ParseBigIntError};

use nom::{
    IResult, Parser,
    Err::{Incomplete, Error, Failure},
    branch::alt,
    bytes::complete::{escaped_transform, is_not, tag},
    character::{complete::{alpha1, char, none_of, one_of, multispace0}},
    combinator::{map, map_res, opt, recognize, value, verify},
    error::{ParseError, FromExternalError, ContextError, VerboseError},
    multi::{many0, many1, separated_list0},
    sequence::{delimited, preceded, terminated, tuple, pair},
};

use super::ast::*;
use super::object::{Object, Key};


trait CompleteError<'a>:
    ParseError<&'a str> +
    ContextError<&'a str> +
    FromExternalError<&'a str, ParseIntError> +
    FromExternalError<&'a str, ParseBigIntError> +
    FromExternalError<&'a str, ParseFloatError> {}

impl<'a, T> CompleteError<'a> for T
where T:
    ParseError<&'a str> +
    ContextError<&'a str> +
    FromExternalError<&'a str, ParseIntError> +
    FromExternalError<&'a str, ParseBigIntError> +
    FromExternalError<&'a str, ParseFloatError> {}


type OpCons = fn(Expr) -> Operator;

fn postpad<I, O, E: ParseError<I>, F>(
    parser: F,
) -> impl FnMut(I) -> IResult<I, O, E>
where
    F: Parser<I, O, E>,
    I: Clone + nom::InputTakeAtPosition,
    <I as nom::InputTakeAtPosition>::Item: nom::AsChar + Clone,
{
    terminated(parser, multispace0)
}

static KEYWORDS: [&'static str; 14] = [
    "for",
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

fn keyword<'a, E: ParseError<&'a str>>(
    value: &'static str
) -> impl FnMut(&'a str) -> IResult<&'a str, &'a str, E> {
    verify(
        is_not("=,;.:-+/*[](){}\"\' \t\n\r"),
        move |out: &str| out == value,
    )
}

fn identifier<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, &'a str, E> {
    verify(
        recognize(pair(
            alt((alpha1, tag("_"))),
            opt(is_not("=.,:;-+/*[](){}\"\' \t\n\r")),
        )),
        |out: &str| !KEYWORDS.contains(&out),
    )(input)
}

fn map_identifier<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, &'a str, E> {
    is_not(",=:$}()\"\' \t\n\r")(input)
}

fn decimal<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, &'a str, E> {
    recognize(tuple((
        one_of("0123456789"),
        many0(one_of("0123456789_")),
    )))(input)
}

fn exponent<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&str, &str, E> {
    recognize(tuple((
        one_of("eE"),
        opt(one_of("+-")),
        decimal,
    )))(input)
}

fn integer<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    map_res(
        decimal,
        |out: &'a str| {
            let s = out.replace("_", "");
            i64::from_str_radix(s.as_str(), 10).map_or_else(
                |_| { BigInt::from_str(s.as_str()).map(Expr::big_integer) },
                |val| Ok(Expr::integer(val)),
            )
        }
    )(input)
}

fn float<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    map_res(
        alt((
            recognize(tuple((
                decimal,
                char('.'),
                opt(decimal),
                opt(exponent),
            ))),
            recognize(tuple((
                char('.'),
                decimal,
                opt(exponent),
            ))),
            recognize(tuple((
                decimal,
                exponent,
            ))),
        )),
        |out: &str| { out.replace("_", "").parse::<f64>().map(Expr::float) }
    )(input)
}

fn raw_string<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, String, E> {
    map(
        escaped_transform(
            recognize(many1(none_of("\"\\$"))),
            '\\',
            alt((
                value("\"", tag("\"")),
                value("\\", tag("\\")),
            )),
        ),
        |x| x.to_string(),
    )(input)
}

fn string_data<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, StringElement, E> {
    map(
        raw_string,
        StringElement::raw
    )(input)
}

fn string_interp<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, StringElement, E> {
    map(
        preceded(
            postpad(tag("${")),
            terminated(
                expression,
                char('}'),
            ),
        ),
        StringElement::Interpolate,
    )(input)
}

fn string<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    map(
        preceded(
            char('\"'),
            terminated(
                many0(alt((string_interp, string_data))),
                char('\"'),
            ),
        ),
        Expr::string
    )(input)
}

fn boolean<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    alt((
        value(Expr::boolean(true), keyword("true")),
        value(Expr::boolean(false), keyword("false")),
    ))(input)
}

fn null<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    value(Expr::null(), keyword("null"))(input)
}

fn atomic<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    alt((
        null,
        boolean,
        float,
        integer,
        string,
    ))(input)
}

fn list_element<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, ListElement, E> {
    alt((
        map(
            preceded(postpad(tag("...")), expression),
            ListElement::Splat,
        ),
        map(
            tuple((
                preceded(postpad(tag("for")), binding),
                preceded(postpad(tag("in")), expression),
                preceded(postpad(char(':')), list_element),
            )),
            |(binding, iterable, expr)| ListElement::Loop {
                binding,
                iterable,
                element: Box::new(expr),
            },
        ),
        map(
            tuple((
                preceded(postpad(tag("if")), expression),
                preceded(postpad(char(':')), list_element),
            )),
            |(condition, expr)| ListElement::Cond {
                condition,
                element: Box::new(expr),
            },
        ),
        map(expression, ListElement::Singleton),
    ))(input)
}

fn list<'a, E: CompleteError<'a>>(
    input: &'a str
) -> IResult<&'a str, Expr, E> {
    map(
        preceded(
            postpad(char('[')),
            terminated(
                separated_list0(
                    postpad(char(',')),
                    list_element
                ),
                tuple((
                    opt(postpad(char(','))),
                    char(']')
                )),
            ),
        ),
        Expr::List,
    )(input)
}

fn map_element<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, MapElement, E> {
    alt((
        map(
            preceded(postpad(tag("...")), expression),
            MapElement::Splat,
        ),
        map(
            tuple((
                preceded(postpad(tag("for")), binding),
                preceded(postpad(tag("in")), expression),
                preceded(postpad(char(':')), map_element),
            )),
            |(binding, iterable, expr)| MapElement::Loop {
                binding,
                iterable,
                element: Box::new(expr),
            },
        ),
        map(
            tuple((
                preceded(postpad(tag("if")), expression),
                preceded(postpad(char(':')), map_element),
            )),
            |(condition, expr)| MapElement::Cond {
                condition,
                element: Box::new(expr)
            },
        ),
        map(
            tuple((
                terminated(
                    preceded(postpad(char('$')), expression),
                    postpad(char(':')),
                ),
                expression,
            )),
            |(key, value)| MapElement::Singleton { key, value },
        ),
        map(
            tuple((
                terminated(
                    postpad(map_identifier),
                    postpad(char(':')),
                ),
                expression,
            )),
            |(key, value)| MapElement::Singleton {
                key: Object::int_string(key).literal(),
                value,
            },
        ),
    ))(input)
}

fn mapping<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    map(
        preceded(
            postpad(char('{')),
            terminated(
                separated_list0(
                    postpad(char(',')),
                    map_element,
                ),
                tuple((
                    opt(postpad(char(','))),
                    char('}'),
                )),
            ),
        ),
        Expr::Map,
    )(input)
}

fn postfixable<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    postpad(alt((
        delimited(postpad(char('(')), expression, postpad(char(')'))),
        atomic,
        map(identifier, Expr::id),
        list,
        mapping,
    )))(input)
}

fn object_access<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Operator, E> {
    map(
        preceded(
            postpad(char('.')),
            identifier,
        ),
        |out: &str| Operator::BinOp(BinOp::Index, Box::new(Object::int_string(out).literal())),
    )(input)
}

fn object_index<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Operator, E> {
    map(
        delimited(
            postpad(char('[')),
            expression,
            char(']'),
        ),
        |expr| Operator::BinOp(BinOp::Index, Box::new(expr)),
    )(input)
}

fn function_arg<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, ArgElement, E> {
    alt((
        map(
            preceded(postpad(tag("...")), expression),
            ArgElement::Splat,
        ),
        map(
            tuple((
                postpad(identifier),
                preceded(
                    postpad(char(':')),
                    expression,
                ),
            )),
            |(name, expr)| ArgElement::keyword(name, expr),
        ),
        map(
            expression,
            ArgElement::Singleton,
        ),
    ))(input)
}

fn function_call<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Operator, E> {
    map(
        delimited(
            postpad(char('(')),
            separated_list0(
                postpad(char(',')),
                function_arg,
            ),
            postpad(char(')')),
        ),
        Operator::FunCall,
    )(input)
}

fn postfixed<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    map(
        tuple((
            postfixable,
            many0(postpad(alt((
                object_access,
                object_index,
                function_call,
            )))),
        )),
        |(expr, ops)| {
            ops.into_iter().fold(
                expr,
                |expr, operator| Expr::Operator { operand: Box::new(expr), operator },
            )
        },
    )(input)
}

fn prefixed<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    map(
        tuple((
            many0(alt((
                value(UnOp::Passthrough, postpad(tag("+"))),
                value(UnOp::ArithmeticalNegate, postpad(tag("-"))),
                value(UnOp::LogicalNegate, postpad(keyword("not"))),
            ))),
            power,
        )),
        |(ops, expr)| {
            ops.into_iter().rev().fold(
                expr,
                |expr, operator| Expr::Operator { operand: Box::new(expr), operator: Operator::UnOp(operator) },
            )
        },
    )(input)
}

fn binop<I, E: ParseError<I>, G, H>(
    operators: G,
    operand: H,
) -> impl FnMut(I) -> IResult<I, Operator, E>
where
    I: Clone + nom::InputTakeAtPosition,
    <I as nom::InputTakeAtPosition>::Item: nom::AsChar + Clone,
    G: Parser<I, OpCons, E>,
    H: Parser<I, Expr, E>,
{
    map(
        tuple((
            postpad(operators),
            operand,
        )),
        |(func, expr)| func(expr),
    )
}

fn binops<I, E: ParseError<I>, G, H>(
    operators: G,
    operand: H,
    right: bool,
) -> impl FnMut(I) -> IResult<I, Expr, E>
where
    I: Clone + nom::InputTakeAtPosition + nom::InputLength,
    <I as nom::InputTakeAtPosition>::Item: nom::AsChar + Clone,
    G: Parser<I, Operator, E>,
    H: Parser<I, Expr, E> + Copy,
{
    map(
        tuple((
            operand,
            many0(operators),
        )),
        move |(expr, ops)| {
            let acc = |expr: Expr, operator: Operator| Expr::Operator { operand: Box::new(expr), operator };
            if right {
                ops.into_iter().rev().fold(expr, acc)
            } else {
                ops.into_iter().fold(expr, acc)
            }
        },
    )
}

fn power<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    binops(
        binop(
            alt((
                value(Operator::power as OpCons, tag("^")),
            )),
            prefixed,
        ),
        postfixed,
        true,
    )(input)
}

fn lbinop<I, E: ParseError<I>, G, H>(
    operators: G,
    operands: H
) -> impl FnMut(I) -> IResult<I, Expr, E>
where
    I: Clone + nom::InputTakeAtPosition + nom::InputLength,
    <I as nom::InputTakeAtPosition>::Item: nom::AsChar + Clone,
    G: Parser<I, OpCons, E>,
    H: Parser<I, Expr, E> + Copy,
{
    binops(binop(operators, operands), operands, false)
}

fn product<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    lbinop(
        alt((
            value(Operator::multiply as OpCons, tag("*")),
            value(Operator::integer_divide as OpCons, tag("//")),
            value(Operator::divide as OpCons, tag("/")),
        )),
        prefixed
    )(input)
}

fn sum<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    lbinop(
        alt((
            value(Operator::add as OpCons, tag("+")),
            value(Operator::subtract as OpCons, tag("-")),
        )),
        product,
    )(input)
}

fn inequality<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    lbinop(
        alt((
            value(Operator::less_equal as OpCons, tag("<=")),
            value(Operator::greater_equal as OpCons, tag(">=")),
            value(Operator::less as OpCons, tag("<")),
            value(Operator::greater as OpCons, tag(">")),
        )),
        sum,
    )(input)
}

fn equality<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    lbinop(
        alt((
            value(Operator::equal as OpCons, tag("==")),
            value(Operator::not_equal as OpCons, tag("!=")),
        )),
        inequality,
    )(input)
}

fn conjunction<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    lbinop(
        alt((
            value(Operator::and as OpCons, tag("and")),
        )),
        equality,
    )(input)
}

fn disjunction<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    lbinop(
        alt((
            value(Operator::or as OpCons, tag("or")),
        )),
        conjunction,
    )(input)
}

fn ident_binding<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Binding, E> {
    postpad(alt((
        map(identifier, |out: &str| Binding::id(out)),
    )))(input)
}

fn list_binding_element<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, ListBindingElement, E> {
    alt((
        map(
            preceded(tag("..."), opt(identifier)),
            |ident| ident.map(ListBindingElement::slurp_to).unwrap_or(ListBindingElement::Slurp),
        ),
        map(
            tuple((binding, opt(preceded(postpad(char('=')), expression)))),
            |(b, e)| ListBindingElement::Binding { binding: b, default: e },
        ),
    ))(input)
}

fn list_binding<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, ListBinding, E> {
    map(
        terminated(
            separated_list0(
                postpad(char(',')),
                list_binding_element,
            ),
            opt(postpad(char(','))),
        ),
        |x| ListBinding(x),
    )(input)
}

fn map_binding_element<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, MapBindingElement, E> {
    alt((
        map(
            preceded(tag("..."), identifier),
            MapBindingElement::slurp_to,
        ),
        map(
            tuple((
                alt((
                    map(
                        tuple((
                            postpad(map_identifier),
                            preceded(
                                postpad(tag("as")),
                                binding,
                            ),
                        )),
                        |(name, binding)| (name, Some(binding)),
                    ),
                    map(
                        postpad(map_identifier),
                        |name: &str| (name, None),
                    ),
                )),
                opt(
                    preceded(
                        postpad(char('=')),
                        expression,
                    ),
                ),
            )),
            |((name, binding), default)| {
                match binding {
                    None => MapBindingElement::Binding {
                        key: Key::new(name.to_string()),
                        binding: Binding::id(name),
                        default,
                    },
                    Some(binding) => MapBindingElement::Binding {
                        key: Key::new(name.to_string()),
                        binding,
                        default,
                    },
                }
            },
        ),
    ))(input)
}

fn map_binding<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, MapBinding, E> {
    map(
        terminated(
            separated_list0(
                postpad(char(',')),
                map_binding_element,
            ),
            opt(postpad(char(','))),
        ),
        |x| MapBinding(x),
    )(input)
}

fn binding<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Binding, E> {
    alt((
        ident_binding,
        map(delimited(postpad(char('[')), list_binding, postpad(char(']'))), Binding::List),
        map(delimited(postpad(char('{')), map_binding, postpad(char('}'))), Binding::Map),
    ))(input)
}

fn function<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    map(
        tuple((
            delimited(
                postpad(char('(')),
                tuple((
                    list_binding,
                    opt(
                        preceded(
                            postpad(char(';')),
                            map_binding,
                        ),
                    ),
                )),
                postpad(char(')')),
            ),
            preceded(
                postpad(tag("=>")),
                expression,
            ),
        )),
        |((posargs, kwargs), expr)| Expr::Function {
            positional: posargs,
            keywords: kwargs,
            expression: Box::new(expr),
        },
    )(input)
}

fn keyword_function<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    map(
        tuple((
            delimited(
                postpad(char('{')),
                map_binding,
                postpad(char('}')),
            ),
            preceded(
                postpad(tag("=>")),
                expression,
            ),
        )),
        |(kwargs, expr)| Expr::Function {
            positional: ListBinding(vec![]),
            keywords: Some(kwargs),
            expression: Box::new(expr),
        },
    )(input)
}

fn let_block<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    map(
        tuple((
            many1(
                tuple((
                    preceded(
                        postpad(keyword("let")),
                        binding,
                    ),
                    preceded(
                        postpad(tag("=")),
                        expression,
                    ),
                )),
            ),
            preceded(
                postpad(tag("in")),
                expression,
            ),
        )),
        |(bindings, expr)| Expr::Let { bindings, expression: Box::new(expr) },
    )(input)
}

fn branch<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    map(
        tuple((
            preceded(
                postpad(keyword("if")),
                expression,
            ),
            preceded(
                postpad(keyword("then")),
                expression,
            ),
            preceded(
                postpad(keyword("else")),
                expression,
            ),
        )),
        |(condition, true_branch, false_branch)| Expr::Branch {
            condition: Box::new(condition),
            true_branch: Box::new(true_branch),
            false_branch: Box::new(false_branch),
        },
    )(input)
}

fn composite<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    alt((
        let_block,
        branch,
        function,
        keyword_function,
    ))(input)
}

fn expression<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    alt((
        composite,
        disjunction,
    ))(input)
}

fn import<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, TopLevel, E> {
    map(
        tuple((
            preceded(
                postpad(keyword("import")),
                postpad(preceded(
                    char('\"'),
                    terminated(raw_string, char('\"'))
                )),
            ),
            preceded(
                postpad(keyword("as")),
                postpad(binding),
            )
        )),
        |(path, binding)| TopLevel::Import(path, binding),
    )(input)
}

fn file<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, File, E> {
    map(
        tuple((
            many0(postpad(import)),
            expression,
        )),
        |(statements, expression)| File { statements, expression },
    )(input)
}

pub fn parse(input: &str) -> Result<File, String> {
    file::<VerboseError<&str>>(input).map_or_else(
        |err| match err {
            Incomplete(_) => Err("incomplete input".to_string()),
            Error(e) | Failure(e) => Err(format!("{:#?}", e)),
        },
        |(remaining, node)| if remaining.len() > 0 {
            Err(format!("unconsumed input: {}", remaining))
        } else {
            node.validate()?;
            Ok(node)
        }
    )
}
