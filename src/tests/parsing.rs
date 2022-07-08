use super::super::*;

#[test]
fn booleans_and_null() {
    assert_eq!(parse("true").unwrap(), AstNode::Literal(Object::Boolean(true)));
    assert_eq!(parse("false").unwrap(), AstNode::Literal(Object::Boolean(false)));
    assert_eq!(parse("null").unwrap(), AstNode::Literal(Object::Null));
}

#[test]
fn integers() {
    assert_eq!(parse("0").unwrap(), AstNode::Literal(Object::Integer(0)));
    assert_eq!(parse("1").unwrap(), AstNode::Literal(Object::Integer(1)));
    assert_eq!(parse("9223372036854775807").unwrap(), AstNode::Literal(Object::Integer(9223372036854775807)));
    assert_eq!(
        parse("9223372036854775808").unwrap(),
        AstNode::Literal(Object::BigInteger(BigInt::from_str_radix("9223372036854775808", 10).unwrap())),
    );
}

#[test]
fn floats() {
    assert_eq!(parse("0.0").unwrap(), AstNode::Literal(Object::Float(0.0)));
    assert_eq!(parse("0.").unwrap(), AstNode::Literal(Object::Float(0.0)));
    assert_eq!(parse(".0").unwrap(), AstNode::Literal(Object::Float(0.0)));
    assert_eq!(parse("0e0").unwrap(), AstNode::Literal(Object::Float(0.0)));
    assert_eq!(parse("0e1").unwrap(), AstNode::Literal(Object::Float(0.0)));
    assert_eq!(parse("1.").unwrap(), AstNode::Literal(Object::Float(1.0)));
    assert_eq!(parse("1e+1").unwrap(), AstNode::Literal(Object::Float(10.0)));
    assert_eq!(parse("1e1").unwrap(), AstNode::Literal(Object::Float(10.0)));
    assert_eq!(parse("1e-1").unwrap(), AstNode::Literal(Object::Float(0.1)));
}

#[test]
fn strings() {
    assert_eq!(parse("\"\"").unwrap(), AstNode::Literal(Object::String("".to_string())));
    assert_eq!(parse("\"dingbob\"").unwrap(), AstNode::Literal(Object::String("dingbob".to_string())));
    assert_eq!(parse("\"ding\\\"bob\"").unwrap(), AstNode::Literal(Object::String("ding\"bob".to_string())));
    assert_eq!(parse("\"ding\\\\bob\"").unwrap(), AstNode::Literal(Object::String("ding\\bob".to_string())));

    assert_eq!(
        parse("\"dingbob${a}\"").unwrap(),
        AstNode::String(vec![
            StringElement::Raw("dingbob".to_string()),
            StringElement::Interpolate(AstNode::Identifier("a".to_string())),
        ]),
    );

    assert_eq!(
        parse("\"dingbob${ a}\"").unwrap(),
        AstNode::String(vec![
            StringElement::Raw("dingbob".to_string()),
            StringElement::Interpolate(AstNode::Identifier("a".to_string())),
        ]),
    );
}

#[test]
fn identifiers() {
    assert_eq!(parse("dingbob").unwrap(), AstNode::Identifier("dingbob".to_string()));
    assert_eq!(parse("lets").unwrap(), AstNode::Identifier("lets".to_string()));
}

#[test]
fn let_blocks() {
    assert_eq!(
        parse("let a = \"b\" in 1").unwrap(),
        AstNode::Let(
            vec![
                (Binding::Identifier("a".to_string()), AstNode::Literal(Object::String("b".to_string()))),
            ],
            Box::new(AstNode::Literal(Object::Integer(1))),
        ),
    );

    assert_eq!(
        parse("let a = 1 let b = 2 in a").unwrap(),
        AstNode::Let(
            vec![
                (Binding::Identifier("a".to_string()), AstNode::Literal(Object::Integer(1))),
                (Binding::Identifier("b".to_string()), AstNode::Literal(Object::Integer(2))),
            ],
            Box::new(AstNode::Identifier("a".to_string())),
        ),
    );
}
