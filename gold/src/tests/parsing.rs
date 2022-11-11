use std::ops::{Add, Div, Mul, Neg, Not, Sub};

use crate::ast::*;
use crate::error::{Taggable, Location, Tagged};
use crate::object::{Object, Key};
use crate::parsing::{parse as parse_file};
use crate::traits::{Boxable, Splattable};


fn parse(input: &str) -> Result<Expr, String> {
    parse_file(input).map(|x| x.expression)
}

trait IdAble {
    fn id<T>(self, loc: T) -> Expr where Location: From<T>;
}

impl<U> IdAble for U where U: KeyAble {
    fn id<T>(self, loc: T) -> Expr where Location: From<T> {
        Expr::Identifier(self.key(loc))
    }
}

trait BindingIdAble {
    fn bid<T>(self, loc: T) -> Tagged<Binding> where Location: From<T>, T: Copy;
}

impl<U> BindingIdAble for U where U: KeyAble {
    fn bid<T>(self, loc: T) -> Tagged<Binding> where Location: From<T>, T: Copy {
        Binding::Identifier(self.key(loc)).tag(loc)
    }
}

trait KeyAble {
    fn key<T>(self, loc: T) -> Tagged<Key> where Location: From<T>;
}

impl<U> KeyAble for U where U: AsRef<str> {
    fn key<T>(self, loc: T) -> Tagged<Key> where Location: From<T> {
        Key::new(self).tag(loc)
    }
}


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
    assert_eq!(parse("9223372036854776000"), Ok(Object::bigint("9223372036854776000").unwrap().literal()));
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
        Ok(Expr::String(vec![
            StringElement::raw("dingbob"),
            StringElement::Interpolate("a".id((10, 1, 1))),
        ])),
    );

    assert_eq!(
        parse("\"dingbob${ a}\""),
        Ok(Expr::String(vec![
            StringElement::raw("dingbob"),
            StringElement::Interpolate("a".id((11, 1, 1))),
        ])),
    );
}

#[test]
fn identifiers() {
    assert_eq!(parse("dingbob"), Ok("dingbob".id((0, 1, 7))));
    assert_eq!(parse("lets"), Ok("lets".id((0, 1, 4))));
    assert_eq!(parse("not1"), Ok("not1".id((0, 1, 4))));
}

#[test]
fn lists() {
    assert_eq!(
        parse("[]"),
        Ok(Expr::list(())),
    );

    assert_eq!(
        parse("[   ]"),
        Ok(Expr::list(()))
    );

    assert_eq!(
        parse("[true]"),
        Ok(Expr::list((true,)))
    );

    assert_eq!(
        parse("[\"\"]"),
        Ok(Expr::list(("",)))
    );

    assert_eq!(
        parse("[1,]"),
        Ok(Expr::list((1,))),
    );

    assert_eq!(
        parse("[  1   ,  ]"),
        Ok(Expr::list((1,))),
    );

    assert_eq!(
        parse("[  1   ,2  ]"),
        Ok(Expr::list((1,2))),
    );

    assert_eq!(
        parse("[  1   ,2  ,]"),
        Ok(Expr::list((1,2))),
    );

    assert_eq!(
        parse("[1, false, 2.3, \"fable\", lel]"),
        Ok(Expr::list((1, false, 2.3, "fable", "lel".id((25, 1, 3))))),
    );

    assert_eq!(
        parse("[1, ...x, y]"),
        Ok(Expr::list((1, "x".id((7, 1, 1)).splat(), "y".id((10, 1, 1))))),
    );

    assert_eq!(
        parse("[1, for x in y: x, 2]"),
        Ok(Expr::list((
            1,
            ListElement::Loop {
                binding: "x".bid((8, 1, 1)),
                iterable: "y".id((13, 1, 1)),
                element: Box::new(ListElement::singleton("x".id((16, 1, 1)))),
            },
            2,
        )))
    );

    assert_eq!(
        parse("[if f(x): x]"),
        Ok(Expr::list((
            ListElement::Cond {
                condition:"f".id((4, 1, 1)).funcall(("x".id((6, 1, 1)),)),
                element: ListElement::singleton("x".id((10, 1, 1))).to_box(),
            },
        ))),
    );
}

#[test]
fn nested_lists() {
    assert_eq!(
        parse("[[]]"),
        Ok(Expr::list((Expr::list(()),))),
    );

    assert_eq!(
        parse("[1, [2]]"),
        Ok(Expr::list((1, Expr::list((2,))))),
    );
}

#[test]
fn maps() {
    assert_eq!(
        parse("{}"),
        Ok(Expr::map(())),
    );

    assert_eq!(
        parse("{  }"),
        Ok(Expr::map(())),
    );

    assert_eq!(
        parse("{a: 1}"),
        Ok(Expr::map((
            ("a", 1),
        ))),
    );

    assert_eq!(
        parse("{a: 1,}"),
        Ok(Expr::map((
            ("a", 1),
        ))),
    );

    assert_eq!(
        parse("{  a :1,}"),
        Ok(Expr::map((
            ("a", 1),
        ))),
    );

    assert_eq!(
        parse("{a: 1  ,b:2}"),
        Ok(Expr::map((
            ("a", 1),
            ("b", 2),
        ))),
    );

    assert_eq!(
        parse("{che9: false}"),
        Ok(Expr::map((
            ("che9", false),
        ))),
    );

    assert_eq!(
        parse("{fable: \"fable\"}"),
        Ok(Expr::map((
            ("fable", "fable"),
        ))),
    );

    assert_eq!(
        parse("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: 1e1}"),
        Ok(Expr::map((
            ("a", 1),
            ("b", true),
            ("c", 20.0),
            ("d", "hoho"),
            ("e", 10.0),
        ))),
    );

    assert_eq!(
        parse("{ident-with-hyphen: 1}"),
        Ok(Expr::map((
            ("ident-with-hyphen", 1),
        ))),
    );

    assert_eq!(
        parse("{$z: y}"),
        Ok(Expr::Map(vec![
            MapElement::Singleton {
                key: "z".id((2, 1, 1)),
                value: "y".id((5, 1, 1)),
            },
        ])),
    );

    assert_eq!(
        parse("{$(z): y}"),
        Ok(Expr::Map(vec![
            MapElement::Singleton {
                key: "z".id((3, 1, 1)),
                value: "y".id((7, 1, 1)),
            },
        ])),
    );

    assert_eq!(
        parse("{...y, x: 1}"),
        Ok(Expr::Map(vec![
            MapElement::Splat("y".id((4, 1, 1))),
            MapElement::Singleton {
                key: Object::int_string("x").literal(),
                value: Object::Integer(1).literal(),
            },
        ])),
    );

    assert_eq!(
        parse("{for [x,y] in z: x: y}"),
        Ok(Expr::Map(vec![
            MapElement::Loop {
                binding: Binding::List(ListBinding(vec![
                    ListBindingElement::Binding {
                        binding: "x".bid((6, 1, 1)),
                        default: None
                    }.tag((6, 1, 1)),
                    ListBindingElement::Binding {
                        binding: "y".bid((8, 1, 1)),
                        default: None
                    }.tag((8, 1, 1)),
                ])).tag((5, 1, 5)),
                iterable: "z".id((14, 1, 1)),
                element: Box::new(MapElement::Singleton {
                    key: Object::int_string("x").literal(),
                    value: "y".id((20, 1, 1)),
                }),
            },
        ])),
    );

    assert_eq!(
        parse("{if f(x): z: y}"),
        Ok(Expr::Map(vec![
            MapElement::Cond {
                condition: "f".id((4, 1, 1)).funcall(("x".id((6, 1, 1)),)),
                element: Box::new(MapElement::Singleton {
                    key: Object::int_string("z").literal(),
                    value: "y".id((13, 1, 1)),
                }),
            },
        ])),
    );
}

#[test]
fn let_blocks() {
    assert_eq!(
        parse("let a = \"b\" in 1"),
        Ok(Expr::Let {
            bindings: vec![
                ("a".bid((4, 1, 1)), "b".to_ast()),
            ],
            expression: 1.to_ast().to_box(),
        }),
    );

    assert_eq!(
        parse("let a = 1 let b = 2 in a"),
        Ok(Expr::Let {
            bindings: vec![
                ("a".bid((4, 1, 1)), 1.to_ast()),
                ("b".bid((14, 1, 1)), 2.to_ast()),
            ],
            expression: "a".id((23, 1, 1)).to_box(),
        }),
    );

    assert_eq!(
        parse("let [a, b=1, ...] = c in [a, b]"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::Binding {
                            binding: "a".bid((5, 1, 1)),
                            default: None
                        }.tag((5, 1, 1)),
                        ListBindingElement::Binding {
                            binding: "b".bid((8, 1, 1)),
                            default: Some(1.to_ast())
                        }.tag((8, 1, 3)),
                        ListBindingElement::Slurp.tag((13, 1, 3)),
                    ])).tag((4, 1, 13)),
                    "c".id((20, 1, 1)),
                ),
            ],
            expression: Box::new(Expr::List(vec![
                ListElement::Singleton("a".id((26, 1, 1))),
                ListElement::Singleton("b".id((29, 1, 1))),
            ])),
        })
    );

    assert_eq!(
        parse("let [_, ...rest] = list in rest"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::Binding {
                            binding: "_".bid((5, 1, 1)),
                            default: None
                        }.tag((5, 1, 1)),
                        ListBindingElement::SlurpTo("rest".key((11, 1, 4))).tag((8, 1, 7)),
                    ])).tag((4, 1, 12)),
                    "list".id((19, 1, 4)),
                ),
            ],
            expression: "rest".id((27, 1, 4)).to_box(),
        }),
    );

    assert_eq!(
        parse("let [...a] = b in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::SlurpTo("a".key((8, 1, 1))).tag((5, 1, 4)),
                    ])).tag((4, 1, 6)),
                    "b".id((13, 1, 1)),
                ),
            ],
            expression: "a".id((18, 1, 1)).to_box(),
        }),
    );

    assert_eq!(
        parse("let [...a,] = b in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::SlurpTo("a".key((8, 1, 1))).tag((5, 1, 4)),
                    ])).tag((4, 1, 7)),
                    "b".id((14, 1, 1)),
                ),
            ],
            expression: "a".id((19, 1, 1)).to_box(),
        }),
    );

    assert_eq!(
        parse("let {a} = x in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::Map(MapBinding(vec![
                        MapBindingElement::Binding {
                            key: "a".key((5, 1, 1)),
                            binding: "a".bid((5, 1, 1)),
                            default: None,
                        }.tag((5, 1, 1)),
                    ])).tag((4, 1, 3)),
                    "x".id((10, 1, 1)),
                ),
            ],
            expression: "a".id((15, 1, 1)).to_box(),
        }),
    );

    assert_eq!(
        parse("let {a as b} = x in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::Map(MapBinding(vec![
                        MapBindingElement::Binding {
                            key: "a".key((5, 1, 1)),
                            binding: "b".bid((10, 1, 1)),
                            default: None,
                        }.tag((5, 1, 6)),
                    ])).tag((4, 1, 8)),
                    "x".id((15, 1, 1)),
                ),
            ],
            expression: "a".id((20, 1, 1)).to_box(),
        }),
    );

    assert_eq!(
        parse("let {a = y} = x in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::Map(MapBinding(vec![
                        MapBindingElement::Binding {
                            key: "a".key((5, 1, 1)),
                            binding: "a".bid((5, 1, 1)),
                            default: Some("y".id((9, 1, 1))),
                        }.tag((5, 1, 5)),
                    ])).tag((4, 1, 7)),
                    "x".id((14, 1, 1)),
                ),
            ],
            expression: "a".id((19, 1, 1)).to_box(),
        }),
    );

    assert_eq!(
        parse("let {a as b = y} = x in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::Map(MapBinding(vec![
                        MapBindingElement::Binding {
                            key: "a".key((5, 1, 1)),
                            binding: "b".bid((10, 1, 1)),
                            default: Some("y".id((14, 1, 1))),
                        }.tag((5, 1, 10)),
                    ])).tag((4, 1, 12)),
                    "x".id((19, 1, 1)),
                ),
            ],
            expression: "a".id((24, 1, 1)).to_box(),
        }),
    );
}

#[test]
fn branching() {
    assert_eq!(
        parse("if a then b else c"),
        Ok(Expr::Branch {
            condition: Box::new("a".id((3, 1, 1))),
            true_branch: Box::new("b".id((10, 1, 1))),
            false_branch: Box::new("c".id((17, 1, 1))),
        }),
    );
}

#[test]
fn indexing() {
    assert_eq!{
        parse("a.b"),
        Ok("a".id((0, 1, 1)).index(Object::int_string("b").literal())),
    };

    assert_eq!(
        parse("a[b]"),
        Ok("a".id((0, 1, 1)).index("b".id((2, 1, 1)))),
    );

    assert_eq!(
        parse("a.b.c"),
        Ok("a".id((0, 1, 1)).index("b").index("c")),
    );

    assert_eq!(
        parse("a[b].c"),
        Ok("a".id((0, 1, 1)).index("b".id((2, 1, 1))).index("c")),
    );

    assert_eq!(
        parse("a.b[c]"),
        Ok("a".id((0, 1, 1)).index("b").index("c".id((4, 1, 1)))),
    );

    assert_eq!(
        parse("a[b][c]"),
        Ok("a".id((0, 1, 1)).index("b".id((2, 1, 1))).index("c".id((5, 1, 1)))),
    );
}

#[test]
fn funcall() {
    assert_eq!(
        parse("func(1, 2, 3)"),
        Ok("func".id((0, 1, 4)).funcall((1, 2, 3))),
    );

    assert_eq!(
        parse("func(1, 2, a: 3)"),
        Ok("func".id((0, 1, 4)).funcall((1, 2, ("a".key((11, 1, 1)), 3)))),
    );

    assert_eq!(
        parse("func(a: 2, b: 3)"),
        Ok("func".id((0, 1, 4)).funcall((
            ("a".key((5, 1, 1)), 2),
            ("b".key((11, 1, 1)), 3)
        ))),
    );

    assert_eq!(
        parse("((x,y) => x+y)(1,2)"),
        Ok(
            Expr::Function {
                positional: ListBinding(vec![
                    ListBindingElement::Binding {
                        binding: "x".bid((2, 1, 1)),
                        default: None
                    }.tag((2, 1, 1)),
                    ListBindingElement::Binding {
                        binding: "y".bid((4, 1, 1)),
                        default: None
                    }.tag((4, 1, 1)),
                ]),
                keywords: None,
                expression: "x".id((10, 1, 1)).add("y".id((12, 1, 1))).to_box(),
            }.funcall((1, 2))
        ),
    );

    assert_eq!(
        parse("func(1, ...y, z: 2, ...q)"),
        Ok("func".id((0, 1, 4)).funcall((
            1,
            "y".id((11, 1, 1)).splat(),
            ("z".key((14, 1, 1)), 2),
            "q".id((23, 1, 1)).splat()
        ))),
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

    assert_eq!(
        parse("2 // 2 * 2"),
        Ok(2.to_ast().idiv(2).mul(2)),
    );

    assert_eq!(
        parse("2 ^ 2 ^ 2"),
        Ok(2.to_ast().pow(2.to_ast().pow(2))),
    );

    assert_eq!(
        parse("-2 ^ 2 ^ 2"),
        Ok(2.to_ast().pow(2.to_ast().pow(2)).neg()),
    );
}

#[test]
fn functions() {
    assert_eq!(
        parse("() => 1"),
        Ok(Expr::Function {
            positional: ListBinding(vec![]),
            keywords: None,
            expression: 1.to_ast().to_box(),
        }),
    );

    assert_eq!(
        parse("(;) => 1"),
        Ok(Expr::Function {
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![])),
            expression: 1.to_ast().to_box(),
        }),
    );

    assert_eq!(
        parse("{} => 1"),
        Ok(Expr::Function {
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![])),
            expression: 1.to_ast().to_box(),
        }),
    );

    assert_eq!(
        parse("(a) => let b = a in b"),
        Ok(Expr::Function {
            positional: ListBinding(vec![
                ListBindingElement::Binding {
                    binding: "a".bid((1, 1, 1)),
                    default: None
                }.tag((1, 1, 1)),
            ]),
            keywords: None,
            expression: Box::new(Expr::Let {
                bindings: vec![
                    (
                        "b".bid((11, 1, 1)),
                        "a".id((15, 1, 1)),
                    ),
                ],
                expression: Box::new("b".id((20, 1, 1))),
            }),
        }),
    );

    assert_eq!(
        parse("{x=1, y=2} => x + y"),
        Ok(Expr::Function {
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![
                MapBindingElement::Binding {
                    key: "x".key((1, 1, 1)),
                    binding: "x".bid((1, 1, 1)),
                    default: Some(1.to_ast()),
                }.tag((1, 1, 3)),
                MapBindingElement::Binding {
                    key: "y".key((6, 1, 1)),
                    binding: "y".bid((6, 1, 1)),
                    default: Some(2.to_ast()),
                }.tag((6, 1, 3)),
            ])),
            expression: "x".id((14, 1, 1)).add("y".id((18, 1, 1))).to_box(),
        }),
    );
}
