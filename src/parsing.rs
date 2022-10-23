use std::num::ParseFloatError;

use ibig::{IBig};
use ibig::error::{ParseError as IBigParseError};

use nom::{
    IResult, Parser,
    Err::{Incomplete, Error, Failure},
    branch::alt,
    bytes::complete::{escaped_transform, is_not, tag},
    character::complete::{char, none_of, one_of, multispace0},
    combinator::{map, map_res, opt, recognize, value, verify},
    error::{ParseError, FromExternalError, ContextError, VerboseError},
    multi::{many0, many1, separated_list0},
    sequence::{delimited, preceded, terminated, tuple},
};

use super::ast::*;
use super::object::Object;

trait CompleteError<'a>:
    ParseError<&'a str> +
    ContextError<&'a str> +
    FromExternalError<&'a str, IBigParseError> +
    FromExternalError<&'a str, ParseFloatError> {}

impl<'a, T> CompleteError<'a> for T
where T:
    ParseError<&'a str> +
    ContextError<&'a str> +
    FromExternalError<&'a str, IBigParseError> +
    FromExternalError<&'a str, ParseFloatError> {}


type OpCons = fn(AstNode) -> Operator;

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

static KEYWORDS: [&'static str; 12] = [
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
        is_not("=.,:;-+/*[](){}\"\' \t\n\r"),
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
) -> IResult<&'a str, AstNode, E> {
    map_res(
        decimal,
        |out: &'a str| {
            let s = out.replace("_", "");
            i64::from_str_radix(s.as_str(), 10).map_or_else(
                |_| { IBig::from_str_radix(s.as_str(), 10).map(AstNode::big_integer) },
                |val| Ok(AstNode::integer(val)),
            )
        }
    )(input)
}

fn float<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
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
        |out: &str| { out.replace("_", "").parse::<f64>().map(AstNode::float) }
    )(input)
}

fn string_data<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, StringElement, E> {
    map(
        escaped_transform(
            recognize(many1(none_of("\"\\$"))),
            '\\',
            alt((
                value("\"", tag("\"")),
                value("\\", tag("\\")),
            )),
        ),
        StringElement::raw,
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
) -> IResult<&'a str, AstNode, E> {
    map(
        preceded(
            char('\"'),
            terminated(
                many0(alt((string_interp, string_data))),
                char('\"'),
            ),
        ),
        AstNode::string
    )(input)
}

fn boolean<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    alt((
        value(AstNode::boolean(true), keyword("true")),
        value(AstNode::boolean(false), keyword("false")),
    ))(input)
}

fn null<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    value(AstNode::null(), keyword("null"))(input)
}

fn atomic<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
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
) -> IResult<&'a str, AstNode, E> {
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
        AstNode::List,
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
                key: Object::string(key).literal(),
                value,
            },
        ),
    ))(input)
}

fn mapping<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
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
        AstNode::Map,
    )(input)
}

fn postfixable<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    postpad(alt((
        delimited(postpad(char('(')), expression, postpad(char(')'))),
        atomic,
        map(identifier, AstNode::id),
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
        |out: &str| Operator::BinOp(BinOp::Index, Box::new(Object::string(out).literal())),
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
            |(name, expr)| ArgElement::Keyword(name.to_string(), expr),
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
) -> IResult<&'a str, AstNode, E> {
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
                |expr, operator| AstNode::Operator { operand: Box::new(expr), operator },
            )
        },
    )(input)
}

fn prefixed<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    map(
        tuple((
            many0(alt((
                value(UnOp::ArithmeticalNegate, postpad(tag("-"))),
                value(UnOp::LogicalNegate, postpad(keyword("not"))),
            ))),
            power,
        )),
        |(ops, expr)| {
            ops.into_iter().rev().fold(
                expr,
                |expr, operator| AstNode::Operator { operand: Box::new(expr), operator: Operator::UnOp(operator) },
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
    H: Parser<I, AstNode, E>,
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
) -> impl FnMut(I) -> IResult<I, AstNode, E>
where
    I: Clone + nom::InputTakeAtPosition + nom::InputLength,
    <I as nom::InputTakeAtPosition>::Item: nom::AsChar + Clone,
    G: Parser<I, Operator, E>,
    H: Parser<I, AstNode, E> + Copy,
{
    map(
        tuple((
            operand,
            many0(operators),
        )),
        move |(expr, ops)| {
            let acc = |expr: AstNode, operator: Operator| AstNode::Operator { operand: Box::new(expr), operator };
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
) -> IResult<&'a str, AstNode, E> {
    binops(
        binop(
            alt((
                value(Operator::power as OpCons, tag("^")),
                value(Operator::multiply as OpCons, tag("*")),
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
) -> impl FnMut(I) -> IResult<I, AstNode, E>
where
    I: Clone + nom::InputTakeAtPosition + nom::InputLength,
    <I as nom::InputTakeAtPosition>::Item: nom::AsChar + Clone,
    G: Parser<I, OpCons, E>,
    H: Parser<I, AstNode, E> + Copy,
{
    binops(binop(operators, operands), operands, false)
}

fn product<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
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
) -> IResult<&'a str, AstNode, E> {
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
) -> IResult<&'a str, AstNode, E> {
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
) -> IResult<&'a str, AstNode, E> {
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
) -> IResult<&'a str, AstNode, E> {
    lbinop(
        alt((
            value(Operator::and as OpCons, tag("and")),
        )),
        equality,
    )(input)
}

fn disjunction<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
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
    map(
        tuple((binding, opt(preceded(postpad(char('=')), expression)))),
        |(b, e)| ListBindingElement::Binding { binding: b, default: e }
    )(input)
}

fn list_binding<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Binding, E> {
    map(
        terminated(
            tuple((
                separated_list0(
                    postpad(char(',')),
                    list_binding_element,
                ),
                opt(
                    preceded(
                        tuple((postpad(char(',')), postpad(tag("...")))),
                        opt(identifier),
                    ),
                ),
            )),
            opt(postpad(char(','))),
        ),
        |(mut bindings, slurp)| {
            match slurp {
                Some(Some(name)) => bindings.push(ListBindingElement::slurp_to(name)),
                Some(None) => bindings.push(ListBindingElement::Slurp),
                _ => {}
            };
            Binding::List(bindings)
        }
    )(input)
}

fn map_binding_element<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, MapBindingElement, E> {
    map(
        tuple((
            alt((
                map(
                    tuple((
                        postpad(map_identifier),
                        preceded(
                            postpad(char(':')),
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
                    key: name.to_string(),
                    binding: Binding::id(name),
                    default,
                },
                Some(binding) => MapBindingElement::Binding {
                    key: name.to_string(),
                    binding,
                    default,
                },
            }
        }
    )(input)
}

fn map_binding<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Binding, E> {
    map(
        terminated(
            tuple((
                separated_list0(
                    postpad(char(',')),
                    map_binding_element
                ),
                opt(
                    preceded(
                        tuple((postpad(char(',')), postpad(tag("...")))),
                        postpad(identifier),
                    ),
                ),
            )),
            opt(postpad(char(','))),
        ),
        |(mut bindings, slurp)| {
            match slurp {
                Some(name) => bindings.push(MapBindingElement::SlurpTo(name.to_string())),
                _ => {}
            };
            Binding::Map(bindings)
        },
    )(input)
}

fn binding<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Binding, E> {
    alt((
        ident_binding,
        delimited(postpad(char('[')), list_binding, postpad(char(']'))),
        delimited(postpad(char('{')), map_binding, postpad(char('}'))),
    ))(input)
}

fn function<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
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
        |((posargs, kwargs), expr)| AstNode::Function {
            positional: posargs,
            keywords: kwargs.unwrap_or_else(|| Binding::Map(vec![])),
            expression: Box::new(expr),
        },
    )(input)
}

fn keyword_function<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
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
        |(kwargs, expr)| AstNode::Function {
            positional: Binding::List(vec![]),
            keywords: kwargs,
            expression: Box::new(expr),
        },
    )(input)
}

fn let_block<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
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
        |(bindings, expr)| AstNode::Let { bindings, expression: Box::new(expr) },
    )(input)
}

fn branch<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
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
        |(condition, true_branch, false_branch)| AstNode::Branch {
            condition: Box::new(condition),
            true_branch: Box::new(true_branch),
            false_branch: Box::new(false_branch),
        },
    )(input)
}

fn composite<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    alt((
        let_block,
        branch,
        function,
        keyword_function,
    ))(input)
}

fn expression<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    alt((
        composite,
        disjunction,
    ))(input)
}

pub fn parse(input: &str) -> Result<AstNode, String> {
    expression::<VerboseError<&str>>(input).map_or_else(
        |err| match err {
            Incomplete(_) => Err("incomplete input".to_string()),
            Error(e) | Failure(e) => Err(format!("{:#?}", e)),
        },
        |(remaining, node)| if remaining.len() > 0 {
            Err(format!("unconsumed input: {}", remaining))
        } else {
            Ok(node)
        }
    )
}
