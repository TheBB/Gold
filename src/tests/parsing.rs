use super::super::*;

#[test]
fn booleans_and_null() {
    assert_eq!(parse("true"), Ok(AstNode::Literal(Object::Boolean(true))));
    assert_eq!(parse("false"), Ok(AstNode::Literal(Object::Boolean(false))));
    assert_eq!(parse("null"), Ok(AstNode::Literal(Object::Null)));
}

#[test]
fn integers() {
    assert_eq!(parse("0"), Ok(AstNode::Literal(Object::Integer(0))));
    assert_eq!(parse("1"), Ok(AstNode::Literal(Object::Integer(1))));
    assert_eq!(parse("9223372036854775807"), Ok(AstNode::Literal(Object::Integer(9223372036854775807))));
    assert_eq!(
        parse("9223372036854775808"),
        Ok(AstNode::Literal(Object::BigInteger(BigInt::from_str_radix("9223372036854775808", 10).unwrap()))),
    );
}

#[test]
fn floats() {
    assert_eq!(parse("0.0"), Ok(AstNode::Literal(Object::Float(0.0))));
    assert_eq!(parse("0."), Ok(AstNode::Literal(Object::Float(0.0))));
    assert_eq!(parse(".0"), Ok(AstNode::Literal(Object::Float(0.0))));
    assert_eq!(parse("0e0"), Ok(AstNode::Literal(Object::Float(0.0))));
    assert_eq!(parse("0e1"), Ok(AstNode::Literal(Object::Float(0.0))));
    assert_eq!(parse("1."), Ok(AstNode::Literal(Object::Float(1.0))));
    assert_eq!(parse("1e+1"), Ok(AstNode::Literal(Object::Float(10.0))));
    assert_eq!(parse("1e1"), Ok(AstNode::Literal(Object::Float(10.0))));
    assert_eq!(parse("1e-1"), Ok(AstNode::Literal(Object::Float(0.1))));
}

#[test]
fn strings() {
    assert_eq!(parse("\"\""), Ok(AstNode::Literal(Object::String("".to_string()))));
    assert_eq!(parse("\"dingbob\""), Ok(AstNode::Literal(Object::String("dingbob".to_string()))));
    assert_eq!(parse("\"ding\\\"bob\""), Ok(AstNode::Literal(Object::String("ding\"bob".to_string()))));
    assert_eq!(parse("\"ding\\\\bob\""), Ok(AstNode::Literal(Object::String("ding\\bob".to_string()))));

    assert_eq!(
        parse("\"dingbob${a}\""),
        Ok(AstNode::String(vec![
            StringElement::Raw("dingbob".to_string()),
            StringElement::Interpolate(AstNode::Identifier("a".to_string())),
        ])),
    );

    assert_eq!(
        parse("\"dingbob${ a}\""),
        Ok(AstNode::String(vec![
            StringElement::Raw("dingbob".to_string()),
            StringElement::Interpolate(AstNode::Identifier("a".to_string())),
        ])),
    );
}

#[test]
fn identifiers() {
    assert_eq!(parse("dingbob"), Ok(AstNode::Identifier("dingbob".to_string())));
    assert_eq!(parse("lets"), Ok(AstNode::Identifier("lets".to_string())));
    assert_eq!(parse("not1"), Ok(AstNode::Identifier("not1".to_string())));
}

#[test]
fn lists() {
    assert_eq!(parse("[]"), Ok(AstNode::List(vec![])));
    assert_eq!(parse("[   ]"), Ok(AstNode::List(vec![])));

    assert_eq!(
        parse("[true]"),
        Ok(AstNode::List(vec![
            ListElement::Singleton(AstNode::Literal(Object::Boolean(true))),
        ])),
    );

    assert_eq!(
        parse("[\"\"]"),
        Ok(AstNode::List(vec![
            ListElement::Singleton(AstNode::Literal(Object::String("".to_string()))),
        ])),
    );

    assert_eq!(
        parse("[1,]"),
        Ok(AstNode::List(vec![
            ListElement::Singleton(AstNode::Literal(Object::Integer(1))),
        ])),
    );

    assert_eq!(
        parse("[  1   ,  ]"),
        Ok(AstNode::List(vec![
            ListElement::Singleton(AstNode::Literal(Object::Integer(1))),
        ])),
    );

    assert_eq!(
        parse("[  1   ,2  ]"),
        Ok(AstNode::List(vec![
            ListElement::Singleton(AstNode::Literal(Object::Integer(1))),
            ListElement::Singleton(AstNode::Literal(Object::Integer(2))),
        ])),
    );

    assert_eq!(
        parse("[  1   ,2  ,]"),
        Ok(AstNode::List(vec![
            ListElement::Singleton(AstNode::Literal(Object::Integer(1))),
            ListElement::Singleton(AstNode::Literal(Object::Integer(2))),
        ])),
    );

    assert_eq!(
        parse("[1, false, 2.3, \"fable\", lel]"),
        Ok(AstNode::List(vec![
            ListElement::Singleton(AstNode::Literal(Object::Integer(1))),
            ListElement::Singleton(AstNode::Literal(Object::Boolean(false))),
            ListElement::Singleton(AstNode::Literal(Object::Float(2.3))),
            ListElement::Singleton(AstNode::Literal(Object::String("fable".to_string()))),
            ListElement::Singleton(AstNode::Identifier("lel".to_string())),
        ])),
    );

    assert_eq!(
        parse("[1, ...x, y]"),
        Ok(AstNode::List(vec![
            ListElement::Singleton(AstNode::Literal(Object::Integer(1))),
            ListElement::Splat(AstNode::Identifier("x".to_string())),
            ListElement::Singleton(AstNode::Identifier("y".to_string())),
        ])),
    );

    assert_eq!(
        parse("[1, for x in y: x, 2]"),
        Ok(AstNode::List(vec![
            ListElement::Singleton(AstNode::Literal(Object::Integer(1))),
            ListElement::Loop {
                binding: Binding::Identifier("x".to_string()),
                iterable: AstNode::Identifier("y".to_string()),
                element: Box::new(ListElement::Singleton(AstNode::Identifier("x".to_string()))),
            },
            ListElement::Singleton(AstNode::Literal(Object::Integer(2))),
        ])),
    );

    assert_eq!(
        parse("[if f(x): x]"),
        Ok(AstNode::List(vec![
            ListElement::Cond {
                condition: AstNode::Operator {
                    operand: Box::new(AstNode::Identifier("f".to_string())),
                    operator: Operator::FunCall(vec![
                        ArgElement::Singleton(AstNode::Identifier("x".to_string())),
                    ]),
                },
                element: Box::new(ListElement::Singleton(AstNode::Identifier("x".to_string()))),
            },
        ])),
    );
}

#[test]
fn nested_lists() {
    assert_eq!(
        parse("[[]]"),
        Ok(AstNode::List(vec![
            ListElement::Singleton(AstNode::List(vec![])),
        ])),
    );

    assert_eq!(
        parse("[1, [2]]"),
        Ok(AstNode::List(vec![
            ListElement::Singleton(AstNode::Literal(Object::Integer(1))),
            ListElement::Singleton(AstNode::List(vec![
                ListElement::Singleton(AstNode::Literal(Object::Integer(2))),
            ])),
        ])),
    );
}

#[test]
fn maps() {
    assert_eq!(parse("{}"), Ok(AstNode::Map(vec![])));
    assert_eq!(parse("{  }"), Ok(AstNode::Map(vec![])));

    assert_eq!(
        parse("{a: 1}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("a".to_string())),
                value: AstNode::Literal(Object::Integer(1)),
            },
        ])),
    );

    assert_eq!(
        parse("{a: 1,}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("a".to_string())),
                value: AstNode::Literal(Object::Integer(1)),
            },
        ])),
    );

    assert_eq!(
        parse("{  a :1,}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("a".to_string())),
                value: AstNode::Literal(Object::Integer(1)),
            },
        ])),
    );

    assert_eq!(
        parse("{a: 1  ,b:2}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("a".to_string())),
                value: AstNode::Literal(Object::Integer(1)),
            },
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("b".to_string())),
                value: AstNode::Literal(Object::Integer(2)),
            },
        ])),
    );

    assert_eq!(
        parse("{che9: false}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("che9".to_string())),
                value: AstNode::Literal(Object::Boolean(false)),
            },
        ])),
    );

    assert_eq!(
        parse("{fable: \"fable\"}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("fable".to_string())),
                value: AstNode::Literal(Object::String("fable".to_string())),
            },
        ])),
    );

    assert_eq!(
        parse("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: 1e1}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("a".to_string())),
                value: AstNode::Literal(Object::Integer(1)),
            },
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("b".to_string())),
                value: AstNode::Literal(Object::Boolean(true)),
            },
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("c".to_string())),
                value: AstNode::Literal(Object::Float(20.0)),
            },
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("d".to_string())),
                value: AstNode::Literal(Object::String("hoho".to_string())),
            },
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("e".to_string())),
                value: AstNode::Literal(Object::Float(10.0)),
            },
        ])),
    );

    assert_eq!(
        parse("{ident-with-hyphen: 1}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("ident-with-hyphen".to_string())),
                value: AstNode::Literal(Object::Integer(1)),
            }
        ])),
    );

    assert_eq!(
        parse("{$z: y}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: AstNode::Identifier("z".to_string()),
                value: AstNode::Identifier("y".to_string()),
            },
        ])),
    );

    assert_eq!(
        parse("{$(z): y}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: AstNode::Identifier("z".to_string()),
                value: AstNode::Identifier("y".to_string()),
            },
        ])),
    );

    assert_eq!(
        parse("{...y, x: 1}"),
        Ok(AstNode::Map(vec![
            MapElement::Splat(AstNode::Identifier("y".to_string())),
            MapElement::Singleton {
                key: AstNode::Literal(Object::String("x".to_string())),
                value: AstNode::Literal(Object::Integer(1)),
            },
        ])),
    );

    assert_eq!(
        parse("{for [x,y] in z: x: y}"),
        Ok(AstNode::Map(vec![
            MapElement::Loop {
                binding: Binding::List(vec![
                    ListBindingElement::Binding { binding: Binding::Identifier("x".to_string()), default: None },
                    ListBindingElement::Binding { binding: Binding::Identifier("y".to_string()), default: None },
                ]),
                iterable: AstNode::Identifier("z".to_string()),
                element: Box::new(MapElement::Singleton {
                    key: AstNode::Literal(Object::String("x".to_string())),
                    value: AstNode::Identifier("y".to_string()),
                }),
            },
        ])),
    );

    assert_eq!(
        parse("{if f(x): z: y}"),
        Ok(AstNode::Map(vec![
            MapElement::Cond {
                condition: AstNode::Operator {
                    operand: Box::new(AstNode::Identifier("f".to_string())),
                    operator: Operator::FunCall(vec![
                        ArgElement::Singleton(AstNode::Identifier("x".to_string())),
                    ]),
                },
                element: Box::new(MapElement::Singleton {
                    key: AstNode::Literal(Object::String("z".to_string())),
                    value: AstNode::Identifier("y".to_string()),
                }),
            },
        ])),
    );
}

#[test]
fn let_blocks() {
    assert_eq!(
        parse("let a = \"b\" in 1"),
        Ok(AstNode::Let {
            bindings: vec![
                (Binding::Identifier("a".to_string()), AstNode::Literal(Object::String("b".to_string()))),
            ],
            expression: Box::new(AstNode::Literal(Object::Integer(1))),
        }),
    );

    assert_eq!(
        parse("let a = 1 let b = 2 in a"),
        Ok(AstNode::Let {
            bindings: vec![
                (Binding::Identifier("a".to_string()), AstNode::Literal(Object::Integer(1))),
                (Binding::Identifier("b".to_string()), AstNode::Literal(Object::Integer(2))),
            ],
            expression: Box::new(AstNode::Identifier("a".to_string())),
        }),
    );

    assert_eq!(
        parse("let [a, b=1, ...] = c in [a, b]"),
        Ok(AstNode::Let {
            bindings: vec![
                (
                    Binding::List(vec![
                        ListBindingElement::Binding { binding: Binding::Identifier("a".to_string()), default: None },
                        ListBindingElement::Binding { binding: Binding::Identifier("b".to_string()), default: Some(AstNode::Literal(Object::Integer(1))) },
                        ListBindingElement::Slurp,
                    ]),
                    AstNode::Identifier("c".to_string()),
                ),
            ],
            expression: Box::new(AstNode::List(vec![
                ListElement::Singleton(AstNode::Identifier("a".to_string())),
                ListElement::Singleton(AstNode::Identifier("b".to_string())),
            ])),
        })
    );

    assert_eq!(
        parse("let [_, ...rest] = list in rest"),
        Ok(AstNode::Let {
            bindings: vec![
                (
                    Binding::List(vec![
                        ListBindingElement::Binding { binding: Binding::Identifier("_".to_string()), default: None },
                        ListBindingElement::SlurpTo("rest".to_string()),
                    ]),
                    AstNode::Identifier("list".to_string()),
                ),
            ],
            expression: Box::new(AstNode::Identifier("rest".to_string()),)
        }),
    );

    assert_eq!(
        parse("let {a} = x in a"),
        Ok(AstNode::Let {
            bindings: vec![
                (
                    Binding::Map(vec![
                        MapBindingElement::Binding {
                            key: "a".to_string(),
                            binding: Binding::Identifier("a".to_string()),
                            default: None,
                        },
                    ]),
                    AstNode::Identifier("x".to_string()),
                ),
            ],
            expression: Box::new(AstNode::Identifier("a".to_string())),
        }),
    );

    assert_eq!(
        parse("let {a: b} = x in a"),
        Ok(AstNode::Let {
            bindings: vec![
                (
                    Binding::Map(vec![
                        MapBindingElement::Binding {
                            key: "a".to_string(),
                            binding: Binding::Identifier("b".to_string()),
                            default: None,
                        },
                    ]),
                    AstNode::Identifier("x".to_string()),
                ),
            ],
            expression: Box::new(AstNode::Identifier("a".to_string())),
        }),
    );

    assert_eq!(
        parse("let {a = y} = x in a"),
        Ok(AstNode::Let {
            bindings: vec![
                (
                    Binding::Map(vec![
                        MapBindingElement::Binding {
                            key: "a".to_string(),
                            binding: Binding::Identifier("a".to_string()),
                            default: Some(AstNode::Identifier("y".to_string())),
                        },
                    ]),
                    AstNode::Identifier("x".to_string()),
                ),
            ],
            expression: Box::new(AstNode::Identifier("a".to_string())),
        }),
    );

    assert_eq!(
        parse("let {a: b = y} = x in a"),
        Ok(AstNode::Let {
            bindings: vec![
                (
                    Binding::Map(vec![
                        MapBindingElement::Binding {
                            key: "a".to_string(),
                            binding: Binding::Identifier("b".to_string()),
                            default: Some(AstNode::Identifier("y".to_string())),
                        },
                    ]),
                    AstNode::Identifier("x".to_string()),
                ),
            ],
            expression: Box::new(AstNode::Identifier("a".to_string())),
        }),
    );
}

#[test]
fn branching() {
    assert_eq!(
        parse("if a then b else c"),
        Ok(AstNode::Branch {
            condition: Box::new(AstNode::Identifier("a".to_string())),
            true_branch: Box::new(AstNode::Identifier("b".to_string())),
            false_branch: Box::new(AstNode::Identifier("c".to_string())),
        }),
    );
}

#[test]
fn indexing() {
    assert_eq!{
        parse("a.b"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Identifier("a".to_string())),
            operator: Operator::Index(Box::new(AstNode::Literal(Object::String("b".to_string())))),
        }),
    };

    assert_eq!(
        parse("a[b]"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Identifier("a".to_string())),
            operator: Operator::Index(Box::new(AstNode::Identifier("b".to_string()))),
        }),
    );

    assert_eq!(
        parse("a.b.c"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Identifier("a".to_string())),
                operator: Operator::Index(Box::new(AstNode::Literal(Object::String("b".to_string())))),
            }),
            operator: Operator::Index(Box::new(AstNode::Literal(Object::String("c".to_string())))),
        }),
    );

    assert_eq!(
        parse("a[b].c"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Identifier("a".to_string())),
                operator: Operator::Index(Box::new(AstNode::Identifier("b".to_string()))),
            }),
            operator: Operator::Index(Box::new(AstNode::Literal(Object::String("c".to_string())))),
        }),
    );

    assert_eq!(
        parse("a.b[c]"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Identifier("a".to_string())),
                operator: Operator::Index(Box::new(AstNode::Literal(Object::String("b".to_string())))),
            }),
            operator: Operator::Index(Box::new(AstNode::Identifier("c".to_string()))),
        }),
    );

    assert_eq!(
        parse("a[b][c]"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Identifier("a".to_string())),
                operator: Operator::Index(Box::new(AstNode::Identifier("b".to_string()))),
            }),
            operator: Operator::Index(Box::new(AstNode::Identifier("c".to_string()))),
        }),
    );
}

#[test]
fn funcall() {
    assert_eq!(
        parse("func(1, 2, 3)"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Identifier("func".to_string())),
            operator: Operator::FunCall(vec![
                ArgElement::Singleton(AstNode::Literal(Object::Integer(1))),
                ArgElement::Singleton(AstNode::Literal(Object::Integer(2))),
                ArgElement::Singleton(AstNode::Literal(Object::Integer(3))),
            ]),
        }),
    );

    assert_eq!(
        parse("func(1, 2, a: 3)"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Identifier("func".to_string())),
            operator: Operator::FunCall(vec![
                ArgElement::Singleton(AstNode::Literal(Object::Integer(1))),
                ArgElement::Singleton(AstNode::Literal(Object::Integer(2))),
                ArgElement::Keyword(
                    "a".to_string(),
                    AstNode::Literal(Object::Integer(3)),
                ),
            ]),
        }),
    );

    assert_eq!(
        parse("func(a: 2, b: 3)"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Identifier("func".to_string())),
            operator: Operator::FunCall(vec![
                ArgElement::Keyword(
                    "a".to_string(),
                    AstNode::Literal(Object::Integer(2)),
                ),
                ArgElement::Keyword(
                    "b".to_string(),
                    AstNode::Literal(Object::Integer(3)),
                ),
            ]),
        }),
    );

    assert_eq!(
        parse("((x,y) => x+y)(1,2)"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Function {
                positional: Binding::List(vec![
                    ListBindingElement::Binding { binding: Binding::Identifier("x".to_string()), default: None },
                    ListBindingElement::Binding { binding: Binding::Identifier("y".to_string()), default: None },
                ]),
                keywords: Binding::Map(vec![]),
                expression: Box::new(AstNode::Operator {
                    operand: Box::new(AstNode::Identifier("x".to_string())),
                    operator: Operator::Add(Box::new(AstNode::Identifier("y".to_string()))),
                }),
            }),
            operator: Operator::FunCall(vec![
                ArgElement::Singleton(AstNode::Literal(Object::Integer(1))),
                ArgElement::Singleton(AstNode::Literal(Object::Integer(2))),
        ]),
    }),
    );

    assert_eq!(
        parse("func(1, ...y, z: 2, ...q)"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Identifier("func".to_string())),
            operator: Operator::FunCall(vec![
                ArgElement::Singleton(AstNode::Literal(Object::Integer(1))),
                ArgElement::Splat(AstNode::Identifier("y".to_string())),
                ArgElement::Keyword("z".to_string(), AstNode::Literal(Object::Integer(2))),
                ArgElement::Splat(AstNode::Identifier("q".to_string())),
            ]),
        }),
    );
}

#[test]
fn unary_operators() {
    assert_eq!(
        parse("-1"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Literal(Object::Integer(1))),
            operator: Operator::ArithmeticalNegate,
        }),
    );

    assert_eq!(
        parse("- not 1"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Literal(Object::Integer(1))),
                operator: Operator::LogicalNegate,
            }),
            operator: Operator::ArithmeticalNegate,
        }),
    );

    assert_eq!(
        parse("not -1"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Literal(Object::Integer(1))),
                operator: Operator::ArithmeticalNegate,
            }),
            operator: Operator::LogicalNegate,
        }),
    );
}

#[test]
fn power_operators() {
    assert_eq!(
        parse("2^3"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Literal(Object::Integer(2))),
            operator: Operator::Power(
                Box::new(AstNode::Literal(Object::Integer(3))),
            ),
        }),
    );

    assert_eq!(
        parse("2^-3"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Literal(Object::Integer(2))),
            operator: Operator::Power(
                Box::new(AstNode::Operator {
                    operand: Box::new(AstNode::Literal(Object::Integer(3))),
                    operator: Operator::ArithmeticalNegate,
                }),
            ),
        }),
    );

    assert_eq!(
        parse("-2^3"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Literal(Object::Integer(2))),
                operator: Operator::Power(
                    Box::new(AstNode::Literal(Object::Integer(3))),
                ),
            }),
            operator: Operator::ArithmeticalNegate,
        }),
    );

    assert_eq!(
        parse("-2^-3"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Literal(Object::Integer(2))),
                operator: Operator::Power(
                    Box::new(AstNode::Operator {
                        operand: Box::new(AstNode::Literal(Object::Integer(3))),
                        operator: Operator::ArithmeticalNegate,
                    }),
                ),
            }),
            operator: Operator::ArithmeticalNegate,
        }),
    );
}

#[test]
fn operators() {
    assert_eq!(
        parse("1 + 2"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Literal(Object::Integer(1))),
            operator: Operator::Add(Box::new(
                AstNode::Literal(Object::Integer(2)),
            )),
        }),
    );

    assert_eq!(
        parse("1 / 2 + 3"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Literal(Object::Integer(1))),
                operator: Operator::Divide(Box::new(
                    AstNode::Literal(Object::Integer(2))
                )),
            }),
            operator: Operator::Add(Box::new(
                AstNode::Literal(Object::Integer(3)),
            )),
        }),
    );

    assert_eq!(
        parse("1 + 2 - 3 * 4 // 5 / 6"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Literal(Object::Integer(1))),
                operator: Operator::Add(Box::new(AstNode::Literal(Object::Integer(2)))),
            }),
            operator: Operator::Subtract(Box::new(
                AstNode::Operator {
                    operand: Box::new(AstNode::Operator {
                        operand: Box::new(AstNode::Operator {
                            operand: Box::new(AstNode::Literal(Object::Integer(3))),
                            operator: Operator::Multiply(Box::new(AstNode::Literal(Object::Integer(4)))),
                        }),
                        operator: Operator::IntegerDivide(Box::new(AstNode::Literal(Object::Integer(5)))),
                    }),
                    operator: Operator::Divide(Box::new(AstNode::Literal(Object::Integer(6)))),
                },
            )),
        }),
    );

    assert_eq!(
        parse("1 < 2"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Literal(Object::Integer(1))),
            operator: Operator::Less(Box::new(
                AstNode::Literal(Object::Integer(2)),
            )),
        }),
    );

    assert_eq!(
        parse("1 > 2 <= 3 >= 4 == 5 != 6"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Operator {
                    operand: Box::new(AstNode::Operator {
                        operand: Box::new(AstNode::Operator {
                            operand: Box::new(AstNode::Literal(Object::Integer(1))),
                            operator: Operator::Greater(Box::new(
                                AstNode::Literal(Object::Integer(2)),
                            )),
                        }),
                        operator: Operator::LessEqual(Box::new(
                            AstNode::Literal(Object::Integer(3)),
                        )),
                    }),
                    operator: Operator::GreaterEqual(Box::new(
                        AstNode::Literal(Object::Integer(4)),
                    )),
                }),
                operator: Operator::Equal(Box::new(
                    AstNode::Literal(Object::Integer(5)),
                )),
            }),
            operator: Operator::NotEqual(Box::new(
                AstNode::Literal(Object::Integer(6)),
            )),
        }),
    );

    assert_eq!(
        parse("1 and 2 or 3"),
        Ok(AstNode::Operator {
            operand: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Literal(Object::Integer(1))),
                operator: Operator::And(Box::new(AstNode::Literal(Object::Integer(2)))),
            }),
            operator: Operator::Or(Box::new(AstNode::Literal(Object::Integer(3)))),
        }),
    );
}

#[test]
fn functions() {
    assert_eq!(
        parse("() => 1"),
        Ok(AstNode::Function {
            positional: Binding::List(vec![]),
            keywords: Binding::Map(vec![]),
            expression: Box::new(AstNode::Literal(Object::Integer(1))),
        }),
    );

    assert_eq!(
        parse("(;) => 1"),
        Ok(AstNode::Function {
            positional: Binding::List(vec![]),
            keywords: Binding::Map(vec![]),
            expression: Box::new(AstNode::Literal(Object::Integer(1))),
        }),
    );

    assert_eq!(
        parse("{} => 1"),
        Ok(AstNode::Function {
            positional: Binding::List(vec![]),
            keywords: Binding::Map(vec![]),
            expression: Box::new(AstNode::Literal(Object::Integer(1))),
        }),
    );

    assert_eq!(
        parse("(a) => let b = a in b"),
        Ok(AstNode::Function {
            positional: Binding::List(vec![
                ListBindingElement::Binding { binding: Binding::Identifier("a".to_string()), default: None },
            ]),
            keywords: Binding::Map(vec![]),
            expression: Box::new(AstNode::Let {
                bindings: vec![
                    (
                        Binding::Identifier("b".to_string()),
                        AstNode::Identifier("a".to_string()),
                    ),
                ],
                expression: Box::new(AstNode::Identifier("b".to_string())),
            }),
        }),
    );

    assert_eq!(
        parse("{x=1, y=2} => x + y"),
        Ok(AstNode::Function {
            positional: Binding::List(vec![]),
            keywords: Binding::Map(vec![
                MapBindingElement::Binding {
                    key: "x".to_string(),
                    binding: Binding::Identifier("x".to_string()),
                    default: Some(AstNode::Literal(Object::Integer(1))),
                },
                MapBindingElement::Binding {
                    key: "y".to_string(),
                    binding: Binding::Identifier("y".to_string()),
                    default: Some(AstNode::Literal(Object::Integer(2))),
                },
            ]),
            expression: Box::new(AstNode::Operator {
                operand: Box::new(AstNode::Identifier("x".to_string())),
                operator: Operator::Add(Box::new(AstNode::Identifier("y".to_string()))),
            }),
        }),
    );
}
