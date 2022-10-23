use std::ops::{Add, Div, Mul, Neg, Not, Sub};

use ibig::IBig;

use crate::ast::*;
use crate::object::{Object};
use crate::parsing::parse;
use crate::traits::{Boxable, Splattable};


#[test]
fn booleans_and_null() {
    assert_eq!(parse("true"), Ok(true.to_ast()));
    assert_eq!(parse("false"), Ok(false.to_ast()));
    assert_eq!(parse("null"), Ok(Object::Null.literal()));
}

#[test]
fn integers() {
    assert_eq!(parse("0"), Ok(0.to_ast()));
    assert_eq!(parse("1"), Ok(1.to_ast()));
    assert_eq!(parse("9223372036854775807"), Ok(9223372036854775807i64.to_ast()));
    assert_eq!(
        parse("9223372036854775808"),
        Ok(Object::BigInteger(IBig::from_str_radix("9223372036854775808", 10).unwrap()).literal()),
    );
}

#[test]
fn floats() {
    assert_eq!(parse("0.0"), Ok(0f64.to_ast()));
    assert_eq!(parse("0.0"), Ok(0f64.to_ast()));
    assert_eq!(parse("0."), Ok(0f64.to_ast()));
    assert_eq!(parse(".0"), Ok(0f64.to_ast()));
    assert_eq!(parse("0e0"), Ok(0f64.to_ast()));
    assert_eq!(parse("0e1"), Ok(0f64.to_ast()));
    assert_eq!(parse("1."), Ok(1f64.to_ast()));
    assert_eq!(parse("1e+1"), Ok(10f64.to_ast()));
    assert_eq!(parse("1e1"), Ok(10f64.to_ast()));
    assert_eq!(parse("1e-1"), Ok(0.1f64.to_ast()));
}

#[test]
fn strings() {
    assert_eq!(parse("\"\""), Ok("".to_ast()));
    assert_eq!(parse("\"dingbob\""), Ok("dingbob".to_ast()));
    assert_eq!(parse("\"ding\\\"bob\""), Ok("ding\"bob".to_ast()));
    assert_eq!(parse("\"ding\\\\bob\""), Ok("ding\\bob".to_ast()));

    assert_eq!(
        parse("\"dingbob${a}\""),
        Ok(AstNode::String(vec![
            StringElement::raw("dingbob"),
            StringElement::Interpolate("a".id()),
        ])),
    );

    assert_eq!(
        parse("\"dingbob${ a}\""),
        Ok(AstNode::String(vec![
            StringElement::raw("dingbob"),
            StringElement::Interpolate("a".id()),
        ])),
    );
}

#[test]
fn identifiers() {
    assert_eq!(parse("dingbob"), Ok("dingbob".id()));
    assert_eq!(parse("lets"), Ok("lets".id()));
    assert_eq!(parse("not1"), Ok("not1".id()));
}

#[test]
fn lists() {
    assert_eq!(
        parse("[]"),
        Ok(AstNode::list(())),
    );

    assert_eq!(
        parse("[   ]"),
        Ok(AstNode::list(()))
    );

    assert_eq!(
        parse("[true]"),
        Ok(AstNode::list((true,)))
    );

    assert_eq!(
        parse("[\"\"]"),
        Ok(AstNode::list(("",)))
    );

    assert_eq!(
        parse("[1,]"),
        Ok(AstNode::list((1,))),
    );

    assert_eq!(
        parse("[  1   ,  ]"),
        Ok(AstNode::list((1,))),
    );

    assert_eq!(
        parse("[  1   ,2  ]"),
        Ok(AstNode::list((1,2))),
    );

    assert_eq!(
        parse("[  1   ,2  ,]"),
        Ok(AstNode::list((1,2))),
    );

    assert_eq!(
        parse("[1, false, 2.3, \"fable\", lel]"),
        Ok(AstNode::list((1, false, 2.3, "fable", "lel".id()))),
    );

    assert_eq!(
        parse("[1, ...x, y]"),
        Ok(AstNode::list((1, "x".id().splat(), "y".id()))),
    );

    assert_eq!(
        parse("[1, for x in y: x, 2]"),
        Ok(AstNode::list((
            1,
            ListElement::Loop {
                binding: Binding::id("x"),
                iterable:"y".id(),
                element: Box::new(ListElement::singleton("x".id())),
            },
            2,
        )))
    );

    assert_eq!(
        parse("[if f(x): x]"),
        Ok(AstNode::list((
            ListElement::Cond {
                condition:"f".id().funcall(("x".id(),)),
                element: ListElement::singleton("x".id()).to_box(),
            },
        ))),
    );
}

#[test]
fn nested_lists() {
    assert_eq!(
        parse("[[]]"),
        Ok(AstNode::list((AstNode::list(()),))),
    );

    assert_eq!(
        parse("[1, [2]]"),
        Ok(AstNode::list((1, AstNode::list((2,))))),
    );
}

#[test]
fn maps() {
    assert_eq!(
        parse("{}"),
        Ok(AstNode::map(())),
    );

    assert_eq!(
        parse("{  }"),
        Ok(AstNode::map(())),
    );

    assert_eq!(
        parse("{a: 1}"),
        Ok(AstNode::map((
            ("a", 1),
        ))),
    );

    assert_eq!(
        parse("{a: 1,}"),
        Ok(AstNode::map((
            ("a", 1),
        ))),
    );

    assert_eq!(
        parse("{  a :1,}"),
        Ok(AstNode::map((
            ("a", 1),
        ))),
    );

    assert_eq!(
        parse("{a: 1  ,b:2}"),
        Ok(AstNode::map((
            ("a", 1),
            ("b", 2),
        ))),
    );

    assert_eq!(
        parse("{che9: false}"),
        Ok(AstNode::map((
            ("che9", false),
        ))),
    );

    assert_eq!(
        parse("{fable: \"fable\"}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: Object::string("fable").literal(),
                value: Object::string("fable").literal(),
            },
        ])),
    );

    assert_eq!(
        parse("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: 1e1}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: Object::string("a").literal(),
                value: Object::Integer(1).literal(),
            },
            MapElement::Singleton {
                key: Object::string("b").literal(),
                value: Object::Boolean(true).literal(),
            },
            MapElement::Singleton {
                key: Object::string("c").literal(),
                value: Object::Float(20.0).literal(),
            },
            MapElement::Singleton {
                key: Object::string("d").literal(),
                value: Object::string("hoho").literal(),
            },
            MapElement::Singleton {
                key: Object::string("e").literal(),
                value: Object::Float(10.0).literal(),
            },
        ])),
    );

    assert_eq!(
        parse("{ident-with-hyphen: 1}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: "ident-with-hyphen".to_ast(),
                value: 1.to_ast(),
            }
        ])),
    );

    assert_eq!(
        parse("{$z: y}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: "z".id(),
                value: "y".id(),
            },
        ])),
    );

    assert_eq!(
        parse("{$(z): y}"),
        Ok(AstNode::Map(vec![
            MapElement::Singleton {
                key: "z".id(),
                value: "y".id(),
            },
        ])),
    );

    assert_eq!(
        parse("{...y, x: 1}"),
        Ok(AstNode::Map(vec![
            MapElement::Splat("y".id()),
            MapElement::Singleton {
                key: Object::string("x").literal(),
                value: Object::Integer(1).literal(),
            },
        ])),
    );

    assert_eq!(
        parse("{for [x,y] in z: x: y}"),
        Ok(AstNode::Map(vec![
            MapElement::Loop {
                binding: Binding::List(vec![
                    ListBindingElement::Binding { binding: Binding::id("x"), default: None },
                    ListBindingElement::Binding { binding: Binding::id("y"), default: None },
                ]),
                iterable: "z".id(),
                element: Box::new(MapElement::Singleton {
                    key: Object::string("x").literal(),
                    value: "y".id(),
                }),
            },
        ])),
    );

    assert_eq!(
        parse("{if f(x): z: y}"),
        Ok(AstNode::Map(vec![
            MapElement::Cond {
                condition:"f".id().funcall(("x".id(),)),
                element: Box::new(MapElement::Singleton {
                    key: Object::string("z").literal(),
                    value: "y".id(),
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
                (Binding::id("a"), "b".to_ast()),
            ],
            expression: 1.to_ast().to_box(),
        }),
    );

    assert_eq!(
        parse("let a = 1 let b = 2 in a"),
        Ok(AstNode::Let {
            bindings: vec![
                (Binding::id("a"), 1.to_ast()),
                (Binding::id("b"), 2.to_ast()),
            ],
            expression: "a".id().to_box(),
        }),
    );

    assert_eq!(
        parse("let [a, b=1, ...] = c in [a, b]"),
        Ok(AstNode::Let {
            bindings: vec![
                (
                    Binding::List(vec![
                        ListBindingElement::Binding { binding: Binding::id("a"), default: None },
                        ListBindingElement::Binding { binding: Binding::id("b"), default: Some(1.to_ast()) },
                        ListBindingElement::Slurp,
                    ]),
                    "c".id(),
                ),
            ],
            expression: Box::new(AstNode::List(vec![
                ListElement::Singleton("a".id()),
                ListElement::Singleton("b".id()),
            ])),
        })
    );

    assert_eq!(
        parse("let [_, ...rest] = list in rest"),
        Ok(AstNode::Let {
            bindings: vec![
                (
                    Binding::List(vec![
                        ListBindingElement::Binding { binding: Binding::id("_"), default: None },
                        ListBindingElement::slurp_to("rest"),
                    ]),
                    "list".id(),
                ),
            ],
            expression: "rest".id().to_box(),
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
                            binding: Binding::id("a"),
                            default: None,
                        },
                    ]),
                    "x".id(),
                ),
            ],
            expression: "a".id().to_box(),
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
                            binding: Binding::id("b"),
                            default: None,
                        },
                    ]),
                    "x".id(),
                ),
            ],
            expression: "a".id().to_box(),
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
                            binding: Binding::id("a"),
                            default: Some("y".id()),
                        },
                    ]),
                    "x".id(),
                ),
            ],
            expression: "a".id().to_box(),
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
                            binding: Binding::id("b"),
                            default: Some("y".id()),
                        },
                    ]),
                    "x".id(),
                ),
            ],
            expression: "a".id().to_box(),
        }),
    );
}

#[test]
fn branching() {
    assert_eq!(
        parse("if a then b else c"),
        Ok(AstNode::Branch {
            condition: Box::new("a".id()),
            true_branch: Box::new("b".id()),
            false_branch: Box::new("c".id()),
        }),
    );
}

#[test]
fn indexing() {
    assert_eq!{
        parse("a.b"),
        Ok("a".id().index(Object::string("b").literal())),
    };

    assert_eq!(
        parse("a[b]"),
        Ok("a".id().index("b".id())),
    );

    assert_eq!(
        parse("a.b.c"),
        Ok("a".id().index("b").index("c")),
    );

    assert_eq!(
        parse("a[b].c"),
        Ok("a".id().index("b".id()).index("c")),
    );

    assert_eq!(
        parse("a.b[c]"),
        Ok("a".id().index("b").index("c".id())),
    );

    assert_eq!(
        parse("a[b][c]"),
        Ok("a".id().index("b".id()).index("c".id())),
    );
}

#[test]
fn funcall() {
    assert_eq!(
        parse("func(1, 2, 3)"),
        Ok("func".id().funcall((1, 2, 3))),
    );

    assert_eq!(
        parse("func(1, 2, a: 3)"),
        Ok("func".id().funcall((1, 2, ("a", 3)))),
    );

    assert_eq!(
        parse("func(a: 2, b: 3)"),
        Ok("func".id().funcall((("a", 2), ("b", 3)))),
    );

    assert_eq!(
        parse("((x,y) => x+y)(1,2)"),
        Ok(
            AstNode::Function {
                positional: Binding::List(vec![
                    ListBindingElement::Binding { binding: Binding::id("x"), default: None },
                    ListBindingElement::Binding { binding: Binding::id("y"), default: None },
                ]),
                keywords: Binding::Map(vec![]),
                expression: "x".id().add("y".id()).to_box(),
            }.funcall((1, 2))
        ),
    );

    assert_eq!(
        parse("func(1, ...y, z: 2, ...q)"),
        Ok("func".id().funcall((1, "y".id().splat(), ("z", 2), "q".id().splat()))),
    );
}

#[test]
fn unary_operators() {
    assert_eq!(
        parse("-1"),
        Ok(1.to_ast().neg()),
    );

    assert_eq!(
        parse("- not 1"),
        Ok(1.to_ast().not().neg()),
    );

    assert_eq!(
        parse("not -1"),
        Ok(1.to_ast().neg().not()),
    );
}

#[test]
fn power_operators() {
    assert_eq!(
        parse("2^3"),
        Ok(2.to_ast().pow(3)),
    );

    assert_eq!(
        parse("2^-3"),
        Ok(2.to_ast().pow(3.to_ast().neg())),
    );

    assert_eq!(
        parse("-2^3"),
        Ok(2.to_ast().pow(3).neg()),
    );

    assert_eq!(
        parse("-2^-3"),
        Ok(2.to_ast().pow(3.to_ast().neg()).neg()),
    );
}

#[test]
fn operators() {
    assert_eq!(
        parse("1 + 2"),
        Ok(1.to_ast().add(2)),
    );

    assert_eq!(
        parse("1 / 2 + 3"),
        Ok(1.to_ast().div(2).add(3)),
    );

    assert_eq!(
        parse("1 + 2 - 3 * 4 // 5 / 6"),
        Ok(1.to_ast().add(2).sub(3.to_ast().mul(4).idiv(5).div(6))),
    );

    assert_eq!(
        parse("1 < 2"),
        Ok(1.to_ast().lt(2)),
    );

    assert_eq!(
        parse("1 > 2 <= 3 >= 4 == 5 != 6"),
        Ok(1.to_ast().gt(2).lte(3).gte(4).eql(5).neql(6)),
    );

    assert_eq!(
        parse("1 and 2 or 3"),
        Ok(1.to_ast().and(2).or(3)),
    );
}

#[test]
fn functions() {
    assert_eq!(
        parse("() => 1"),
        Ok(AstNode::Function {
            positional: Binding::List(vec![]),
            keywords: Binding::Map(vec![]),
            expression: 1.to_ast().to_box(),
        }),
    );

    assert_eq!(
        parse("(;) => 1"),
        Ok(AstNode::Function {
            positional: Binding::List(vec![]),
            keywords: Binding::Map(vec![]),
            expression: 1.to_ast().to_box(),
        }),
    );

    assert_eq!(
        parse("{} => 1"),
        Ok(AstNode::Function {
            positional: Binding::List(vec![]),
            keywords: Binding::Map(vec![]),
            expression: 1.to_ast().to_box(),
        }),
    );

    assert_eq!(
        parse("(a) => let b = a in b"),
        Ok(AstNode::Function {
            positional: Binding::List(vec![
                ListBindingElement::Binding { binding: Binding::id("a"), default: None },
            ]),
            keywords: Binding::Map(vec![]),
            expression: Box::new(AstNode::Let {
                bindings: vec![
                    (
                        Binding::id("b"),
                        "a".id(),
                    ),
                ],
                expression: Box::new("b".id()),
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
                    binding: Binding::id("x"),
                    default: Some(1.to_ast()),
                },
                MapBindingElement::Binding {
                    key: "y".to_string(),
                    binding: Binding::id("y"),
                    default: Some(2.to_ast()),
                },
            ]),
            expression: "x".id().add("y".id()).to_box(),
        }),
    );
}
