use std::num::ParseFloatError;

use num_bigint::{BigInt, ParseBigIntError};
use num_traits::Num;

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

trait CompleteError<'a>:
    ParseError<&'a str> +
    ContextError<&'a str> +
    FromExternalError<&'a str, ParseBigIntError> +
    FromExternalError<&'a str, ParseFloatError> {}

impl<'a, T> CompleteError<'a> for T
    where T:
    ParseError<&'a str> +
    ContextError<&'a str> +
    FromExternalError<&'a str, ParseBigIntError> +
    FromExternalError<&'a str, ParseFloatError> {}

#[derive(Debug, Clone, PartialEq)]
pub enum Object {
    Integer(i64),
    BigInteger(BigInt),
    Float(f64),
    String(String),
    Boolean(bool),
    Null,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Binding {
    Identifier(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum StringElement {
    Raw(String),
    Interpolate(AstNode),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ListElement {
    Singleton(AstNode),
}

#[derive(Debug, Clone, PartialEq)]
pub enum MapElement {
    Singleton(AstNode, AstNode),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Operator {
    Index(Box<AstNode>),
    ArithmeticalNegate,
    LogicalNegate,
    Power(Box<AstNode>),
    Multiply(Box<AstNode>),
    IntegerDivide(Box<AstNode>),
    Divide(Box<AstNode>),
    Add(Box<AstNode>),
    Subtract(Box<AstNode>),
    Less(Box<AstNode>),
    Greater(Box<AstNode>),
    LessEqual(Box<AstNode>),
    GreaterEqual(Box<AstNode>),
    Equal(Box<AstNode>),
    NotEqual(Box<AstNode>),
    And(Box<AstNode>),
    Or(Box<AstNode>),
}

type OpCons = fn(Box<AstNode>) -> Operator;

#[derive(Debug, Clone, PartialEq)]
pub enum AstNode {
    Literal(Object),
    String(Vec<StringElement>),
    Identifier(String),
    List(Vec<ListElement>),
    Map(Vec<MapElement>),
    Let(Vec<(Binding, AstNode)>, Box<AstNode>),
    Operator(Box<AstNode>, Operator),
}

impl AstNode {
    fn integer(value: i64) -> AstNode { AstNode::Literal(Object::Integer(value)) }
    fn big_integer(value: BigInt) -> AstNode { AstNode::Literal(Object::BigInteger(value)) }
    fn float(value: f64) -> AstNode { AstNode::Literal(Object::Float(value)) }
    fn boolean(value: bool) -> AstNode { AstNode::Literal(Object::Boolean(value)) }
    fn null() -> AstNode { AstNode::Literal(Object::Null) }

    fn string(value: Vec<StringElement>) -> AstNode {
        if value.len() == 0 {
            AstNode::Literal(Object::String("".to_string()))
        } else if value.len() == 1 {
            match &value[0] {
                StringElement::Raw(val) => AstNode::Literal(Object::String(val.clone())),
                _ => AstNode::String(value)
            }
        } else {
            AstNode::String(value)
        }
    }
}

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
        is_not(",.-+/*[](){}\"\' \t\n\r"),
        move |out: &str| out == value,
    )
}

fn identifier<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, &'a str, E> {
    verify(
        is_not(".-+/*[](){}\"\' \t\n\r"),
        |out: &str| !KEYWORDS.contains(&out),
    )(input)
}

fn map_identifier<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, &'a str, E> {
    is_not("=$\"\' \t\n\r")(input)
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
                |_| { BigInt::from_str_radix(s.as_str(), 10).map(AstNode::big_integer) },
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
        StringElement::Raw,
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
            tuple((
                terminated(
                    postpad(map_identifier),
                    postpad(char('=')),
                ),
                expression,
            )),
            |(key, value)| MapElement::Singleton({
                let value = key.to_string(); AstNode::Literal(Object::String(value.to_string())) }, value),
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
        atomic,
        map(identifier, |out: &str| AstNode::Identifier(out.to_string())),
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
        |out: &str| Operator::Index(Box::new(AstNode::Literal(Object::String(out.to_string())))),
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
        |expr| Operator::Index(Box::new(expr)),
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
            )))),
        )),
        |(expr, ops)| {
            ops.into_iter().fold(
                expr,
                |expr, op| AstNode::Operator(Box::new(expr), op),
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
                value(Operator::ArithmeticalNegate, postpad(tag("-"))),
                value(Operator::LogicalNegate, postpad(keyword("not"))),
            ))),
            power,
        )),
        |(ops, expr)| {
            ops.into_iter().rev().fold(
                expr,
                |expr, op| AstNode::Operator(Box::new(expr), op),
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
        |(func, expr)| func(Box::new(expr)),
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
            let acc = |expr: AstNode, op: Operator| AstNode::Operator(Box::new(expr), op);
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
                value(Operator::Power as OpCons, tag("^")),
                value(Operator::Multiply as OpCons, tag("*")),
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
            value(Operator::Multiply as OpCons, tag("*")),
            value(Operator::IntegerDivide as OpCons, tag("//")),
            value(Operator::Divide as OpCons, tag("/")),
        )),
        prefixed
    )(input)
}

fn sum<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    lbinop(
        alt((
            value(Operator::Add as OpCons, tag("+")),
            value(Operator::Subtract as OpCons, tag("-")),
        )),
        product,
    )(input)
}

fn inequality<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    lbinop(
        alt((
            value(Operator::LessEqual as OpCons, tag("<=")),
            value(Operator::GreaterEqual as OpCons, tag(">=")),
            value(Operator::Less as OpCons, tag("<")),
            value(Operator::Greater as OpCons, tag(">")),
        )),
        sum,
    )(input)
}

fn equality<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    lbinop(
        alt((
            value(Operator::Equal as OpCons, tag("==")),
            value(Operator::NotEqual as OpCons, tag("!=")),
        )),
        inequality,
    )(input)
}

fn conjunction<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    lbinop(
        alt((
            value(Operator::And as OpCons, tag("and")),
        )),
        equality,
    )(input)
}

fn disjunction<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    lbinop(
        alt((
            value(Operator::Or as OpCons, tag("or")),
        )),
        conjunction,
    )(input)
}

fn binding<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, Binding, E> {
    postpad(alt((
        map(identifier, |out: &str| Binding::Identifier(out.to_string())),
    )))(input)
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
        |(bindings, expr)| AstNode::Let(bindings, Box::new(expr)),
    )(input)
}

fn composite<'a, E: CompleteError<'a>>(
    input: &'a str,
) -> IResult<&'a str, AstNode, E> {
    alt((
        let_block,
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

#[cfg(test)]
mod tests;
