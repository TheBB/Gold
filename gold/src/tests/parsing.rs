use std::ops::{Add, Div, Mul, Neg, Not, Sub};

use crate::ast::*;
use crate::error::{Location, Tagged, SyntaxError, SyntaxErrorReason, Expected};
use crate::object::{Object, Key};
use crate::parsing::{parse as parse_file};
use crate::traits::{Boxable, Taggable};


fn parse(input: &str) -> Result<Tagged<Expr>, SyntaxError> {
    parse_file(input).map(|x| x.expression)
}

trait IdAble {
    fn id<T>(self, loc: T) -> Tagged<Expr> where Location: From<T>, T: Copy;
}

impl<U> IdAble for U where U: KeyAble {
    fn id<T>(self, loc: T) -> Tagged<Expr> where Location: From<T>, T: Copy {
        Expr::Identifier(self.key(loc)).tag(loc)
    }
}

trait LitAble {
    fn lit<T>(self, loc: T) -> Tagged<Expr> where Location: From<T>, T: Copy;
}

impl<U> LitAble for U where U: KeyAble {
    fn lit<T>(self, loc: T) -> Tagged<Expr> where Location: From<T>, T: Copy {
        self.key(loc).map(Object::IntString).map(Expr::Literal)
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

trait ListElementAble {
    fn lel<T>(self, loc: T) -> Tagged<ListElement> where Location: From<T>, T: Copy;
}

impl<U> ListElementAble for U where Object: From<U> {
    fn lel<T>(self, loc: T) -> Tagged<ListElement> where Location: From<T>, T: Copy {
        ListElement::Singleton(Expr::Literal(Object::from(self)).tag(loc)).tag(loc)
    }
}

trait MapElementAble {
    fn mel(self) -> Tagged<MapElement>;
}

impl MapElementAble for (Tagged<Expr>, Tagged<Expr>) {
    fn mel(self) -> Tagged<MapElement> {
        let loc = Location::from((&self.0, &self.1));
        MapElement::Singleton {
            key: self.0,
            value: self.1
        }.tag(loc)
    }
}

trait ExprAble {
    fn expr<T>(self, loc: T) -> Tagged<Expr> where Location: From<T>;
}

impl<U> ExprAble for U where Object: From<U> {
    fn expr<T>(self, loc: T) -> Tagged<Expr> where Location: From<T> {
        Expr::Literal(Object::from(self)).tag(loc)
    }
}


#[test]
fn booleans_and_null() {
    assert_eq!(parse("true"), Ok(true.expr((0, 1, 4))));
    assert_eq!(parse("false"), Ok(false.expr((0, 1, 5))));
    assert_eq!(parse("null"), Ok(Object::Null.expr((0, 1, 4))));
}

#[test]
fn integers() {
    assert_eq!(parse("0"), Ok(0.expr((0, 1, 1))));
    assert_eq!(parse("1"), Ok(1.expr((0, 1, 1))));
    assert_eq!(parse("1  "), Ok(1.expr((0, 1, 1))));
    assert_eq!(parse("9223372036854775807"), Ok(9223372036854775807i64.expr((0, 1, 19))));
    assert_eq!(parse("9223372036854776000"), Ok(Object::bigint("9223372036854776000").unwrap().expr((0, 1, 19))));
}

#[test]
fn floats() {
    assert_eq!(parse("0.0"), Ok(0f64.expr((0, 1, 3))));
    assert_eq!(parse("0."), Ok(0f64.expr((0, 1, 2))));
    assert_eq!(parse(".0"), Ok(0f64.expr((0, 1, 2))));
    assert_eq!(parse("0e0"), Ok(0f64.expr((0, 1, 3))));
    assert_eq!(parse("0e1"), Ok(0f64.expr((0, 1, 3))));
    assert_eq!(parse("1."), Ok(1f64.expr((0, 1, 2))));
    assert_eq!(parse("1e+1"), Ok(10f64.expr((0, 1, 4))));
    assert_eq!(parse("1e1"), Ok(10f64.expr((0, 1, 3))));
    assert_eq!(parse("1e-1"), Ok(0.1f64.expr((0, 1, 4))));
}

#[test]
fn strings() {
    assert_eq!(parse("\"\""), Ok("".expr((0, 1, 2))));
    assert_eq!(parse("\"dingbob\""), Ok("dingbob".expr((0, 1, 9))));
    assert_eq!(parse("\"ding\\\"bob\""), Ok("ding\"bob".expr((0, 1, 11))));
    assert_eq!(parse("\"ding\\\\bob\""), Ok("ding\\bob".expr((0, 1, 11))));

    assert_eq!(
        parse("\"dingbob${a}\""),
        Ok(Expr::String(vec![
            StringElement::raw("dingbob"),
            StringElement::Interpolate("a".id((10, 1, 1))),
        ]).tag((0, 1, 13))),
    );

    assert_eq!(
        parse("\"dingbob${ a}\""),
        Ok(Expr::String(vec![
            StringElement::raw("dingbob"),
            StringElement::Interpolate("a".id((11, 1, 1))),
        ]).tag((0, 1, 14))),
    );

    assert_eq!(
        parse("\"alpha\" \"bravo\""),
        Ok(Expr::String(vec![
            StringElement::raw("alpha"),
            StringElement::raw("bravo"),
        ]).tag((0, 1, 15)))
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
        Ok(Expr::list(()).tag((0, 1, 2))),
    );

    assert_eq!(
        parse("[   ]"),
        Ok(Expr::list(()).tag((0, 1, 5))),
    );

    assert_eq!(
        parse("[true]"),
        Ok(Expr::list((
            true.lel((1, 1, 4)),
        )).tag((0, 1, 6))),
    );

    assert_eq!(
        parse("[\"\"]"),
        Ok(Expr::list((
            "".lel((1, 1, 2)),
        )).tag((0, 1, 4))),
    );

    assert_eq!(
        parse("[1,]"),
        Ok(Expr::list((
            1.lel((1, 1, 1)),
        )).tag((0, 1, 4))),
    );

    assert_eq!(
        parse("[  1   ,  ]"),
        Ok(Expr::list((
            1.lel((3, 1, 1)),
        )).tag((0, 1, 11))),
    );

    assert_eq!(
        parse("[  1   ,2  ]"),
        Ok(Expr::list((
            1.lel((3, 1, 1)),   // TODO
            2.lel((8, 1, 1)),
        )).tag((0, 1, 12))),
    );

    assert_eq!(
        parse("[  1   ,2  ,]"),
        Ok(Expr::list((
            1.lel((3, 1, 1)),
            2.lel((8, 1, 1)),
        )).tag((0, 1, 13))),
    );

    assert_eq!(
        parse("[1, false, 2.3, \"fable\", lel]"),
        Ok(Expr::list((
            1.lel((1, 1, 1)),
            false.lel((4, 1, 5)),
            2.3.lel((11, 1, 3)),
            "fable".lel((16, 1, 7)),
            ListElement::Singleton("lel".id((25, 1, 3))).tag((25, 1, 3)),
        )).tag((0, 1, 29))),
    );

    assert_eq!(
        parse("[1, ...x, y]"),
        Ok(Expr::list((
            1.lel((1, 1, 1)),
            "x".id((7, 1, 1)).wrap(ListElement::Splat, (4, 1, 4)),
            "y".id((10, 1, 1)).wraptag(ListElement::Singleton),
        )).tag((0, 1, 12))),
    );

    assert_eq!(
        parse("[1, for x in y: x, 2]"),
        Ok(Expr::list((
            1.lel((1, 1, 1)),
            ListElement::Loop {
                binding: "x".bid((8, 1, 1)),
                iterable: "y".id((13, 1, 1)),
                element: "x".id((16, 1, 1)).wraptag(ListElement::Singleton).to_box(),
            }.tag((4, 1, 13)),
            2.lel((19, 1, 1)),
        )).tag((0, 1, 21))),
    );

    assert_eq!(
        parse("[when f(x): x]"),
        Ok(Expr::list((
            ListElement::Cond {
                condition: "f".id((6, 1, 1)).funcall((
                    "x".id((8, 1, 1)).wraptag(ArgElement::Singleton),
                )).tag((6, 1, 4)),
                element: "x".id((12, 1, 1)).wraptag(ListElement::Singleton).to_box(),
            }.tag((1, 1, 12)),
        )).tag((0, 1, 14))),
    );

    assert_eq!(
        parse("[ 1 , ... x , when x : y , for x in y : z , ]"),
        Ok(Expr::list((
            1.lel((2, 1, 1)),
            "x".id((10, 1, 1)).wrap(ListElement::Splat, (6, 1, 5)),
            ListElement::Cond {
                condition: "x".id((19, 1, 1)),
                element: "y".id((23, 1, 1)).wraptag(ListElement::Singleton).to_box(),
            }.tag((14, 1, 10)),
            ListElement::Loop {
                binding: "x".bid((31, 1, 1)),
                iterable: "y".id((36, 1, 1)),
                element: "z".id((40, 1, 1)).wraptag(ListElement::Singleton).to_box(),
            }.tag((27, 1, 14)),
        )).tag((0, 1, 45))),
    );

    assert_eq!(
        parse("[ (1) , ... (x), when x: (y) , for x in y: (z) ]"),
        Ok(Expr::list((
            1.lel((3, 1, 1)),
            "x".id((13, 1, 1)).wrap(ListElement::Splat, (8, 1, 7)),
            ListElement::Cond {
                condition: "x".id((22, 1, 1)),
                element: "y".id((26, 1, 1)).wraptag(ListElement::Singleton).to_box(),
            }.tag((17, 1, 11)),
            ListElement::Loop {
                binding: "x".bid((35, 1, 1)),
                iterable: "y".id((40, 1, 1)),
                element: "z".id((44, 1, 1)).wraptag(ListElement::Singleton).to_box(),
            }.tag((31, 1, 15)),
        )).tag((0, 1, 48))),
    );
}

#[test]
fn nested_lists() {
    assert_eq!(
        parse("[[]]"),
        Ok(Expr::list((
            Expr::list(()).tag((1, 1, 2)).wraptag(ListElement::Singleton),
        )).tag((0, 1, 4))),
    );

    assert_eq!(
        parse("[1, [2]]"),
        Ok(Expr::list((
            1.lel((1, 1, 1)),
            Expr::list((
                2.lel((5, 1, 1)),
            )).tag((4, 1, 3)).wraptag(ListElement::Singleton),
        )).tag((0, 1, 8))),
    );
}

#[test]
fn maps() {
    assert_eq!(
        parse("{}"),
        Ok(Expr::map(()).tag((0, 1, 2))),
    );

    assert_eq!(
        parse("{  }"),
        Ok(Expr::map(()).tag((0, 1, 4))),
    );

    assert_eq!(
        parse("{a: 1}"),
        Ok(Expr::map((
            ("a".lit((1, 1, 1)), 1.expr((4, 1, 1))).mel(),
        )).tag((0, 1, 6))),
    );

    assert_eq!(
        parse("{a: 1,}"),
        Ok(Expr::map((
            ("a".lit((1, 1, 1)), 1.expr((4, 1, 1))).mel(),
        )).tag((0, 1, 7))),
    );

    assert_eq!(
        parse("{  a :1,}"),
        Ok(Expr::map((
            ("a".lit((3, 1, 1)), 1.expr((6, 1, 1))).mel(),
        )).tag((0, 1, 9))),
    );

    assert_eq!(
        parse("{a: 1  ,b:2}"),
        Ok(Expr::map((
            ("a".lit((1, 1, 1)), 1.expr((4, 1, 1))).mel(),
            ("b".lit((8, 1, 1)), 2.expr((10, 1, 1))).mel(),
        )).tag((0, 1, 12))),
    );

    assert_eq!(
        parse("{che9: false}"),
        Ok(Expr::map((
            ("che9".lit((1, 1, 4)), false.expr((7, 1, 5))).mel(),
        )).tag((0, 1, 13))),
    );

    assert_eq!(
        parse("{fable: \"fable\"}"),
        Ok(Expr::map((
            ("fable".lit((1, 1, 5)), "fable".expr((8, 1, 7))).mel(),
        )).tag((0, 1, 16))),
    );

    assert_eq!(
        parse("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: 1e1}"),
        Ok(Expr::map((
            ("a".lit((1, 1, 1)), 1.expr((4, 1, 1))).mel(),
            ("b".lit((7, 1, 1)), true.expr((10, 1, 4))).mel(),
            ("c".lit((16, 1, 1)), 20.0.expr((19, 1, 4))).mel(),
            ("d".lit((25, 1, 1)), "hoho".expr((28, 1, 6))).mel(),
            ("e".lit((36, 1, 1)), 10.0.expr((39, 1, 3))).mel(),
        )).tag((0, 1, 43))),
    );

    assert_eq!(
        parse("{ident-with-hyphen: 1}"),
        Ok(Expr::map((
            ("ident-with-hyphen".lit((1, 1, 17)), 1.expr((20, 1, 1))).mel(),
        )).tag((0, 1, 22))),
    );

    assert_eq!(
        parse("{$z: y}"),
        Ok(Expr::map((
            MapElement::Singleton {
                key: "z".id((2, 1, 1)),
                value: "y".id((5, 1, 1))
            }.tag((1, 1, 5)),
        )).tag((0, 1, 7))),
    );

    assert_eq!(
        parse("{$(z): y}"),
        Ok(Expr::map((
            MapElement::Singleton {
                key: "z".id((3, 1, 1)),
                value: "y".id((7, 1, 1)),
            }.tag((1, 1, 7)),
        )).tag((0, 1, 9))),
    );

    assert_eq!(
        parse("{...y, x: 1}"),
        Ok(Expr::map((
            MapElement::Splat("y".id((4, 1, 1))).tag((1, 1, 4)),
            ("x".lit((7, 1, 1)), 1.expr((10, 1, 1))).mel(),
        )).tag((0, 1, 12))),
    );

    assert_eq!(
        parse("{for [x,y] in z: x: y}"),
        Ok(Expr::map((
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
                ]).tag((5, 1, 5))).tag((5, 1, 5)),
                iterable: "z".id((14, 1, 1)),
                element: ("x".lit((17, 1, 1)), "y".id((20, 1, 1))).mel().to_box(),
            }.tag((1, 1, 20)),
        )).tag((0, 1, 22))),
    );

    assert_eq!(
        parse("{when f(x): z: y}"),
        Ok(Expr::map((
            MapElement::Cond {
                condition: "f".id((6, 1, 1)).funcall((
                    ArgElement::Singleton("x".id((8, 1, 1))).tag((8, 1, 1)),
                )).tag((6, 1, 4)),
                element: ("z".lit((12, 1, 1)), "y".id((15, 1, 1))).mel().to_box(),
            }.tag((1, 1, 15)),
        )).tag((0, 1, 17))),
    );

    assert_eq!(
        parse("{ a : 1 , ... x , when x : b : y , for x in y : c : z , $ f : 2 , }"),
        Ok(Expr::map((
            ("a".lit((2, 1, 1)), 1.expr((6, 1, 1))).mel(),
            MapElement::Splat("x".id((14, 1, 1))).tag((10, 1, 5)),
            MapElement::Cond {
                condition: "x".id((23, 1, 1)),
                element: ("b".lit((27, 1, 1)), "y".id((31, 1, 1))).mel().to_box(),
            }.tag((18, 1, 14)),
            MapElement::Loop {
                binding: "x".bid((39, 1, 1)),
                iterable: "y".id((44, 1, 1)),
                element: ("c".lit((48, 1, 1)), "z".id((52, 1, 1))).mel().to_box(),
            }.tag((35, 1, 18)),
            MapElement::Singleton {
                key: "f".id((58, 1, 1)),
                value: 2.expr((62, 1, 1))
            }.tag((56, 1, 7)),
        )).tag((0, 1, 67))),
    );

    assert_eq!(
        parse("{ a : (1), ... (x), when x : b : (y), for x in y : c : (z), $ f : (2) }"),
        Ok(Expr::map((
            MapElement::Singleton {
                key: "a".lit((2, 1, 1)),
                value: 1.expr((7, 1, 1))
            }.tag((2, 1, 7)),
            MapElement::Splat("x".id((16, 1, 1))).tag((11, 1, 7)),
            MapElement::Cond {
                condition: "x".id((25, 1, 1)),
                element: MapElement::Singleton {
                    key: "b".lit((29, 1, 1)),
                    value: "y".id((34, 1, 1))
                }.tag((29, 1, 7)).to_box(),
            }.tag((20, 1, 16)),
            MapElement::Loop {
                binding: "x".bid((42, 1, 1)),
                iterable: "y".id((47, 1, 1)),
                element: MapElement::Singleton {
                    key: "c".lit((51, 1, 1)),
                    value: "z".id((56, 1, 1))
                }.tag((51, 1, 7)).to_box(),
            }.tag((38, 1, 20)),
            MapElement::Singleton {
                key: "f".id((62, 1, 1)),
                value: 2.expr((67, 1, 1))
            }.tag((60, 1, 9)),
        )).tag((0, 1, 71))),
    );
}

#[test]
fn let_blocks() {
    assert_eq!(
        parse("let a = \"b\" in 1"),
        Ok(Expr::Let {
            bindings: vec![
                ("a".bid((4, 1, 1)), "b".expr((8, 1, 3))),
            ],
            expression: 1.expr((15, 1, 1)).to_box(),
        }.tag((0, 1, 16))),
    );

    assert_eq!(
        parse("let a = 1 let b = 2 in a"),
        Ok(Expr::Let {
            bindings: vec![
                ("a".bid((4, 1, 1)), 1.expr((8, 1, 1))),
                ("b".bid((14, 1, 1)), 2.expr((18, 1, 1))),
            ],
            expression: "a".id((23, 1, 1)).to_box(),
        }.tag((0, 1, 24))),
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
                            default: Some(1.expr((10, 1, 1)))
                        }.tag((8, 1, 3)),
                        ListBindingElement::Slurp.tag((13, 1, 3)),
                    ]).tag((4, 1, 13))).tag((4, 1, 13)),
                    "c".id((20, 1, 1)),
                ),
            ],
            expression: Box::new(Expr::list((
                "a".id((26, 1, 1)).wraptag(ListElement::Singleton),
                "b".id((29, 1, 1)).wraptag(ListElement::Singleton),
            )).tag((25, 1, 6))),
        }.tag((0, 1, 31))),
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
                    ]).tag((4, 1, 12))).tag((4, 1, 12)),
                    "list".id((19, 1, 4)),
                ),
            ],
            expression: "rest".id((27, 1, 4)).to_box(),
        }.tag((0, 1, 31))),
    );

    assert_eq!(
        parse("let [...a] = b in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::SlurpTo("a".key((8, 1, 1))).tag((5, 1, 4)),
                    ]).tag((4, 1, 6))).tag((4, 1, 6)),
                    "b".id((13, 1, 1)),
                ),
            ],
            expression: "a".id((18, 1, 1)).to_box(),
        }.tag((0, 1, 19))),
    );

    assert_eq!(
        parse("let [...a,] = b in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::SlurpTo("a".key((8, 1, 1))).tag((5, 1, 4)),
                    ]).tag((4, 1, 7))).tag((4, 1, 7)),
                    "b".id((14, 1, 1)),
                ),
            ],
            expression: "a".id((19, 1, 1)).to_box(),
        }.tag((0, 1, 20))),
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
                    ]).tag((4, 1, 3))).tag((4, 1, 3)),
                    "x".id((10, 1, 1)),
                ),
            ],
            expression: "a".id((15, 1, 1)).to_box(),
        }.tag((0, 1, 16))),
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
                    ]).tag((4, 1, 8))).tag((4, 1, 8)),
                    "x".id((15, 1, 1)),
                ),
            ],
            expression: "a".id((20, 1, 1)).to_box(),
        }.tag((0, 1, 21))),
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
                    ]).tag((4, 1, 7))).tag((4, 1, 7)),
                    "x".id((14, 1, 1)),
                ),
            ],
            expression: "a".id((19, 1, 1)).to_box(),
        }.tag((0, 1, 20))),
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
                    ]).tag((4, 1, 12))).tag((4, 1, 12)),
                    "x".id((19, 1, 1)),
                ),
            ],
            expression: "a".id((24, 1, 1)).to_box(),
        }.tag((0, 1, 25))),
    );

    assert_eq!(
        parse("let [ y = (1) ] = x in y"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::Binding {
                            binding: "y".bid((6, 1, 1)),
                            default: Some(1.expr((11, 1, 1))),
                        }.tag((6, 1, 7)),
                    ]).tag((4, 1, 11))).tag((4, 1, 11)),
                    "x".id((18, 1, 1)),
                ),
            ],
            expression: "y".id((23, 1, 1)).to_box(),
        }.tag((0, 1, 24)))
    );

    assert_eq!(
        parse("let { y = (1) } = x in y"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::Map(MapBinding(vec![
                        MapBindingElement::Binding {
                            key: "y".key((6, 1, 1)),
                            binding: "y".bid((6, 1, 1)),
                            default: Some(1.expr((11, 1, 1))),
                        }.tag((6, 1, 7)),
                    ]).tag((4, 1, 11))).tag((4, 1, 11)),
                    "x".id((18, 1, 1)),
                ),
            ],
            expression: "y".id((23, 1, 1)).to_box(),
        }.tag((0, 1, 24)))
    );
}

#[test]
fn branching() {
    assert_eq!(
        parse("if a then b else c"),
        Ok(Expr::Branch {
            condition: "a".id((3, 1, 1)).to_box(),
            true_branch: "b".id((10, 1, 1)).to_box(),
            false_branch: "c".id((17, 1, 1)).to_box(),
        }.tag((0, 1, 18))),
    );
}

#[test]
fn indexing() {
    assert_eq!{
        parse("a.b"),
        Ok(
            "a".id((0, 1, 1))
            .index("b".lit((2, 1, 1))).tag((0, 1, 3))
        ),
    };

    assert_eq!(
        parse("a[b]"),
        Ok(
            "a".id((0, 1, 1))
            .index("b".id((2, 1, 1))).tag((0, 1, 4))
        ),
    );

    assert_eq!(
        parse("a.b.c"),
        Ok(
            "a".id((0, 1, 1))
            .index("b".lit((2, 1, 1))).tag((0, 1, 3))
            .index("c".lit((4, 1, 1))).tag((0, 1, 5))
        ),
    );

    assert_eq!(
        parse("a[b].c"),
        Ok(
            "a".id((0, 1, 1))
            .index("b".id((2, 1, 1))).tag((0, 1, 4))
            .index("c".lit((5, 1, 1))).tag((0, 1, 6))
        ),
    );

    assert_eq!(
        parse("a.b[c]"),
        Ok(
            "a".id((0, 1, 1))
            .index("b".lit((2, 1, 1))).tag((0, 1, 3))
            .index("c".id((4, 1, 1))).tag((0, 1, 6))
        ),
    );

    assert_eq!(
        parse("a[b][c]"),
        Ok(
            "a".id((0, 1, 1))
            .index("b".id((2, 1, 1))).tag((0, 1, 4))
            .index("c".id((5, 1, 1))).tag((0, 1, 7))
        ),
    );
}

#[test]
fn funcall() {
    assert_eq!(
        parse("func(1, 2, 3,)"),
        Ok("func".id((0, 1, 4)).funcall((
            1.expr((5, 1, 1)).wraptag(ArgElement::Singleton),
            2.expr((8, 1, 1)).wraptag(ArgElement::Singleton),
            3.expr((11, 1, 1)).wraptag(ArgElement::Singleton),
        )).tag((0, 1, 14))),
    );

    assert_eq!(
        parse("func(1, 2, a: 3)"),
        Ok("func".id((0, 1, 4)).funcall((
            1.expr((5, 1, 1)).wraptag(ArgElement::Singleton),
            2.expr((8, 1, 1)).wraptag(ArgElement::Singleton),
            ArgElement::Keyword(
                "a".key((11, 1, 1)),
                3.expr((14, 1, 1)),
            ).tag((11, 1, 4)),
        )).tag((0, 1, 16))),
    );

    assert_eq!(
        parse("func(a: 2, b: 3)"),
        Ok("func".id((0, 1, 4)).funcall((
            ArgElement::Keyword(
                "a".key((5, 1, 1)),
                2.expr((8, 1, 1)),
            ).tag((5, 1, 4)),
            ArgElement::Keyword(
                "b".key((11, 1, 1)),
                3.expr((14, 1, 1)),
            ).tag((11, 1, 4)),
        )).tag((0, 1, 16))),
    );

    assert_eq!(
        parse("(fn (x,y) => x+y)(1,2)"),
        Ok(
            Expr::Function {
                positional: ListBinding(vec![
                    ListBindingElement::Binding {
                        binding: "x".bid((5, 1, 1)),
                        default: None
                    }.tag((5, 1, 1)),
                    ListBindingElement::Binding {
                        binding: "y".bid((7, 1, 1)),
                        default: None
                    }.tag((7, 1, 1)),
                ]),
                keywords: None,
                expression: "x".id((13, 1, 1)).add("y".id((15, 1, 1))).tag((13, 1, 3)).to_box(),
            }.tag((1, 1, 15)).funcall((
                1.expr((18, 1, 1)).wraptag(ArgElement::Singleton),
                2.expr((20, 1, 1)).wraptag(ArgElement::Singleton),
            )).tag((0, 1, 22))
        ),
    );

    assert_eq!(
        parse("func(1, ...y, z: 2, ...q)"),
        Ok("func".id((0, 1, 4)).funcall((
            1.expr((5, 1, 1)).wraptag(ArgElement::Singleton),
            ArgElement::Splat("y".id((11, 1, 1))).tag((8, 1, 4)),
            ArgElement::Keyword(
                "z".key((14, 1, 1)),
                2.expr((17, 1, 1)),
            ).tag((14, 1, 4)),
            ArgElement::Splat("q".id((23, 1, 1))).tag((20, 1, 4)),
        )).tag((0, 1, 25))),
    );
}

#[test]
fn unary_operators() {
    assert_eq!(
        parse("-1"),
        Ok(1.expr((1, 1, 1)).neg().tag((0, 1, 2))),
    );

    assert_eq!(
        parse("- not 1"),
        Ok(1.expr((6, 1, 1)).not().tag((2, 1, 5)).neg().tag((0, 1, 7))),
    );

    assert_eq!(
        parse("not -1"),
        Ok(1.expr((5, 1, 1)).neg().tag((4, 1, 2)).not().tag((0, 1, 6))),
    );
}

#[test]
fn power_operators() {
    assert_eq!(
        parse("2^3"),
        Ok(
            2.expr((0, 1, 1))
            .pow(3.expr((2, 1, 1))).tag((0, 1, 3))
        ),
    );

    assert_eq!(
        parse("2^-3"),
        Ok(
            2.expr((0, 1, 1))
            .pow(
                3.expr((3, 1, 1))
                .neg().tag((2, 1, 2))
            ).tag((0, 1, 4))
        ),
    );

    assert_eq!(
        parse("-2^3"),
        Ok(
            2.expr((1, 1, 1))
            .pow(3.expr((3, 1, 1))).tag((1, 1, 3))
            .neg().tag((0, 1, 4))
        ),
    );

    assert_eq!(
        parse("-2^-3"),
        Ok(
            2.expr((1, 1, 1))
            .pow(
                3.expr((4, 1, 1))
                .neg().tag((3, 1, 2))
            ).tag((1, 1, 4))
            .neg().tag((0, 1, 5))
        ),
    );
}

#[test]
fn operators() {
    assert_eq!(
        parse("1 + 2"),
        Ok(
            1.expr((0, 1, 1))
            .add(2.expr((4, 1, 1))).tag((0, 1, 5))
        ),
    );

    assert_eq!(
        parse("1 / 2 + 3"),
        Ok(
            1.expr((0, 1, 1))
            .div(2.expr((4, 1, 1))).tag((0, 1, 5))
            .add(3.expr((8, 1, 1))).tag((0, 1, 9))
        ),
    );

    assert_eq!(
        parse("1 + 2 - 3 * 4 // 5 / 6"),
        Ok(
            1.expr((0, 1, 1))
            .add(2.expr((4, 1, 1))).tag((0, 1, 5))
            .sub(
                3.expr((8, 1, 1))
                .mul(4.expr((12, 1, 1))).tag((8, 1, 5))
                .idiv(5.expr((17, 1, 1))).tag((8, 1, 10))
                .div(6.expr((21, 1, 1))).tag((8, 1, 14))
            ).tag((0, 1, 22))
        ),
    );

    assert_eq!(
        parse("1 < 2"),
        Ok(
            1.expr((0, 1, 1))
            .lt(2.expr((4, 1, 1))).tag((0, 1, 5))
        ),
    );

    assert_eq!(
        parse("1 > 2 <= 3 >= 4 == 5 != 6"),
        Ok(
            1.expr((0, 1, 1))
            .gt(2.expr((4, 1, 1))).tag((0, 1, 5))
            .lte(3.expr((9, 1, 1))).tag((0, 1, 10))
            .gte(4.expr((14, 1, 1))).tag((0, 1, 15))
            .eql(5.expr((19, 1, 1))).tag((0, 1, 20))
            .neql(6.expr((24, 1, 1))).tag((0, 1, 25))
        ),
    );

    assert_eq!(
        parse("1 and 2 or 3"),
        Ok(
            1.expr((0, 1, 1))
            .and(2.expr((6, 1, 1))).tag((0, 1, 7))
            .or(3.expr((11, 1, 1))).tag((0, 1, 12))
        ),
    );

    assert_eq!(
        parse("2 // 2 * 2"),
        Ok(
            2.expr((0, 1, 1))
            .idiv(2.expr((5, 1, 1))).tag((0, 1, 6))
            .mul(2.expr((9, 1, 1))).tag((0, 1, 10))
        ),
    );

    assert_eq!(
        parse("2 ^ 2 ^ 2"),
        Ok(
            2.expr((0, 1, 1))
            .pow(
                2.expr((4, 1, 1))
                .pow(2.expr((8, 1, 1))).tag((4, 1, 5))
            ).tag((0, 1, 9))
        ),
    );

    assert_eq!(
        parse("-2 ^ 2 ^ 2"),
        Ok(
            2.expr((1, 1, 1))
            .pow(
                2.expr((5, 1, 1))
                .pow(2.expr((9, 1, 1))).tag((5, 1, 5))
            ).tag((1, 1, 9))
            .neg().tag((0, 1, 10))
        ),
    );

    assert_eq!(
        parse("(1 + 2) * 5"),
        Ok(
            1.expr((1, 1, 1))
            .add(2.expr((5, 1, 1))).tag((1, 1, 5))
            .mul(5.expr((10, 1, 1))).tag((0, 1, 11))
        ),
    );
}

#[test]
fn functions() {
    assert_eq!(
        parse("fn () => 1"),
        Ok(Expr::Function {
            positional: ListBinding(vec![]),
            keywords: None,
            expression: 1.expr((9, 1, 1)).to_box(),
        }.tag((0, 1, 10))),
    );

    assert_eq!(
        parse("fn (;) => 1"),
        Ok(Expr::Function {
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![])),
            expression: 1.expr((10, 1, 1)).to_box(),
        }.tag((0, 1, 11))),
    );

    assert_eq!(
        parse("fn {} => 1"),
        Ok(Expr::Function {
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![])),
            expression: 1.expr((9, 1, 1)).to_box(),
        }.tag((0, 1, 10))),
    );

    assert_eq!(
        parse("fn (a) => let b = a in b"),
        Ok(Expr::Function {
            positional: ListBinding(vec![
                ListBindingElement::Binding {
                    binding: "a".bid((4, 1, 1)),
                    default: None
                }.tag((4, 1, 1)),
            ]),
            keywords: None,
            expression: Box::new(Expr::Let {
                bindings: vec![
                    (
                        "b".bid((14, 1, 1)),
                        "a".id((18, 1, 1)),
                    ),
                ],
                expression: "b".id((23, 1, 1)).to_box(),
            }.tag((10, 1, 14))),
        }.tag((0, 1, 24))),
    );

    assert_eq!(
        parse("fn {x=1, y=2} => x + y"),
        Ok(Expr::Function {
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![
                MapBindingElement::Binding {
                    key: "x".key((4, 1, 1)),
                    binding: "x".bid((4, 1, 1)),
                    default: Some(1.expr((6, 1, 1))),
                }.tag((4, 1, 3)),
                MapBindingElement::Binding {
                    key: "y".key((9, 1, 1)),
                    binding: "y".bid((9, 1, 1)),
                    default: Some(2.expr((11, 1, 1))),
                }.tag((9, 1, 3)),
            ])),
            expression: "x".id((17, 1, 1)).add("y".id((21, 1, 1))).tag((17, 1, 5)).to_box(),
        }.tag((0, 1, 22))),
    );
}


fn check_err<T>(code: &str, offset: usize, line: u32, expected: T) where SyntaxErrorReason: From<T> {
    assert_eq!(
        parse(code),
        Err(SyntaxError(Some(vec![
            (Location::new(offset, line, 0), SyntaxErrorReason::from(expected)),
        ])))
    );
}


#[test]
fn errors() {
    check_err("let", 3, 1, Expected::Binding);
    check_err("let a", 5, 1, Expected::Equals);
    check_err("let a =", 7, 1, Expected::Expression);
    check_err("let a = 1", 9, 1, Expected::In);
    check_err("let a = 1 in", 12, 1, Expected::Expression);

    check_err("if", 2, 1, Expected::Expression);
    check_err("if true", 7, 1, Expected::Then);
    check_err("if true then", 12, 1, Expected::Expression);
    check_err("if true then 1", 14, 1, Expected::Else);
    check_err("if true then 1 else", 19, 1, Expected::Expression);

    check_err("[", 1, 1, (Expected::CloseBracket, Expected::ListElement));
    check_err("[1", 2, 1, (Expected::CloseBracket, Expected::Comma));
    check_err("[1,", 3, 1, (Expected::CloseBracket, Expected::ListElement));
    check_err("[...", 4, 1, Expected::Expression);
    check_err("[when", 5, 1, Expected::Expression);
    check_err("[when x", 7, 1, Expected::Colon);
    check_err("[when x:", 8, 1, Expected::ListElement);
    check_err("[when x: 1", 10, 1, (Expected::CloseBracket, Expected::Comma));
    check_err("[for", 4, 1, Expected::Binding);
    check_err("[for x", 6, 1, Expected::In);
    check_err("[for x in", 9, 1, Expected::Expression);
    check_err("[for x in y", 11, 1, Expected::Colon);
    check_err("[for x in y:", 12, 1, Expected::ListElement);
    check_err("[for x in y: z", 14, 1, (Expected::CloseBracket, Expected::Comma));

    check_err("{", 1, 1, (Expected::CloseBrace, Expected::MapElement));
    check_err("{x", 2, 1, Expected::Colon);
    check_err("{x:", 3, 1, Expected::Expression);
    check_err("{x: y", 5, 1, (Expected::CloseBrace, Expected::Comma));
    check_err("{x: y,", 6, 1, (Expected::CloseBrace, Expected::MapElement));
    check_err("{$", 2, 1, Expected::Expression);
    check_err("{$x", 3, 1, Expected::Colon);
    check_err("{$x:", 4, 1, Expected::Expression);
    check_err("{$x: y", 6, 1, (Expected::CloseBrace, Expected::Comma));
    check_err("{$x: y,", 7, 1, (Expected::CloseBrace, Expected::MapElement));
    check_err("{...", 4, 1, Expected::Expression);
    check_err("{when", 5, 1, Expected::Expression);
    check_err("{when x", 7, 1, Expected::Colon);
    check_err("{when x:", 8, 1, Expected::MapElement);
    check_err("{when x: y", 10, 1, Expected::Colon);
    check_err("{when x: y:", 11, 1, Expected::Expression);
    check_err("{when x: y: 1", 13, 1, (Expected::CloseBrace, Expected::Comma));
    check_err("{for", 4, 1, Expected::Binding);
    check_err("{for x", 6, 1, Expected::In);
    check_err("{for x in", 9, 1, Expected::Expression);
    check_err("{for x in y", 11, 1, Expected::Colon);
    check_err("{for x in y:", 12, 1, Expected::MapElement);
    check_err("{for x in y: z", 14, 1, Expected::Colon);
    check_err("{for x in y: z:", 15, 1, Expected::Expression);
    check_err("{for x in y: z: v", 17, 1, (Expected::CloseBrace, Expected::Comma));

    check_err("let", 3, 1, Expected::Binding);
    check_err("let [", 5, 1, (Expected::CloseBracket, Expected::ListBindingElement));
    check_err("let [x", 6, 1, (Expected::CloseBracket, Expected::Comma));
    check_err("let [x,", 7, 1, (Expected::CloseBracket, Expected::ListBindingElement));
    check_err("let [x =", 8, 1, Expected::Expression);
    check_err("let [x = 1", 10, 1, (Expected::CloseBracket, Expected::Comma));
    check_err("let [...", 8, 1, (Expected::CloseBracket, Expected::Comma));
    check_err("let {", 5, 1, (Expected::CloseBrace, Expected::MapBindingElement));
    check_err("let {y", 6, 1, (Expected::CloseBrace, Expected::Comma));
    check_err("let {y,", 7, 1, (Expected::CloseBrace, Expected::MapBindingElement));
    check_err("let {y =", 8, 1, Expected::Expression);
    check_err("let {y = 1", 10, 1, (Expected::CloseBrace, Expected::Comma));
    check_err("let {y as", 9, 1, Expected::Binding);
    check_err("let {y as x =", 13, 1, Expected::Expression);
    check_err("let {...", 8, 1, Expected::Identifier);
    check_err("let {...x", 9, 1, (Expected::CloseBrace, Expected::Comma));

    check_err("(", 1, 1, Expected::Expression);
    check_err("(1", 2, 1, Expected::CloseParen);

    check_err("fn", 2, 1, (Expected::OpenParen, Expected::OpenBrace));
    check_err("fn (", 4, 1, (Expected::CloseParen, Expected::Semicolon, Expected::PosParam));
    check_err("fn (x", 5, 1, (Expected::CloseParen, Expected::Semicolon, Expected::Comma));
    check_err("fn (x,", 6, 1, (Expected::CloseParen, Expected::Semicolon, Expected::PosParam));
    check_err("fn (;", 5, 1, (Expected::CloseParen, Expected::KeywordParam));
    check_err("fn (;y", 6, 1, (Expected::CloseParen, Expected::Comma));
    check_err("fn (;y,", 7, 1, (Expected::CloseParen, Expected::KeywordParam));
    check_err("fn ()", 5, 1, Expected::DoubleArrow);
    check_err("fn () =>", 8, 1, Expected::Expression);
    check_err("fn {", 4, 1, (Expected::CloseBrace, Expected::KeywordParam));
    check_err("fn {x", 5, 1, (Expected::CloseBrace, Expected::Comma));
    check_err("fn {x,", 6, 1, (Expected::CloseBrace, Expected::KeywordParam));
    check_err("fn {}", 5, 1, Expected::DoubleArrow);
    check_err("fn {} =>", 8, 1, Expected::Expression);

    check_err("\"alpha", 6, 1, Expected::DoubleQuote);
    check_err("\"alpha$", 7, 1, Expected::OpenBrace);
    check_err("\"alpha${", 8, 1, Expected::Expression);
    check_err("\"alpha${1", 9, 1, Expected::CloseBrace);
    check_err("\"alpha${1}", 10, 1, Expected::DoubleQuote);

    check_err("a.", 2, 1, Expected::Identifier);
    check_err("a[", 2, 1, Expected::Expression);
    check_err("a[1", 3, 1, Expected::CloseBracket);
    check_err("a(", 2, 1, (Expected::CloseParen, Expected::ArgElement));
    check_err("a(1", 3, 1, (Expected::CloseParen, Expected::Comma));
    check_err("a(1,", 4, 1, (Expected::CloseParen, Expected::ArgElement));
    check_err("a(x:", 4, 1, Expected::Expression);
    check_err("a(...", 5, 1, Expected::Expression);

    check_err("-", 1, 1, Expected::Operand);
    check_err("1+", 2, 1, Expected::Operand);

    check_err("import", 6, 1, Expected::ImportPath);
    check_err("import \"path\"", 13, 1, Expected::As);
    check_err("import \"path\" as", 16, 1, Expected::Binding);
    check_err("import \"path\" as y", 18, 1, Expected::Expression);
}
