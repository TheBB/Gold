use std::ops::Range;

use crate::ast::*;
use crate::error::{Location, Tagged, Error, ErrorReason, SyntaxErrorReason, SyntaxElement, Action};
use crate::object::{Object, Key};
use crate::parsing::{parse as parse_file};
use crate::traits::{Boxable, Taggable};


fn parse(input: &str) -> Result<Tagged<Expr>, Error> {
    parse_file(input).map(|x| x.expression)
}

trait IdAble {
    fn id<T>(self, loc: T) -> Tagged<Expr> where Location: From<T>;
}

impl<U> IdAble for U where U: KeyAble {
    fn id<T>(self, loc: T) -> Tagged<Expr> where Location: From<T> {
        self.key(loc).wraptag(Expr::Identifier)
    }
}

trait LitAble {
    fn lit<T>(self, loc: T) -> Tagged<Expr> where Location: From<T>;
}

impl<U> LitAble for U where U: KeyAble {
    fn lit<T>(self, loc: T) -> Tagged<Expr> where Location: From<T> {
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
    fn lel<T>(self, loc: T) -> Tagged<ListElement> where Location: From<T>;
}

impl<U> ListElementAble for U where Object: From<U> {
    fn lel<T>(self, loc: T) -> Tagged<ListElement> where Location: From<T> {
        Expr::Literal(Object::from(self)).tag(loc).wraptag(ListElement::Singleton)
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


impl From<(usize, u32, usize)> for Location {
    fn from((offset, line, length): (usize, u32, usize)) -> Self {
        Location { offset, line, length }
    }
}

impl From<usize> for Location {
    fn from(value: usize) -> Self {
        Location {
            offset: value,
            line: 1,
            length: 1,
        }
    }
}

impl From<Range<u32>> for Location {
    fn from(value: Range<u32>) -> Self {
        Location {
            offset: value.start as usize,
            line: 1,
            length: (value.end - value.start) as usize,
        }
    }
}


#[test]
fn booleans_and_null() {
    assert_eq!(parse("true"), Ok(true.expr(0..4)));
    assert_eq!(parse("false"), Ok(false.expr(0..5)));
    assert_eq!(parse("null"), Ok(Object::Null.expr(0..4)));
}

#[test]
fn integers() {
    assert_eq!(parse("0"), Ok(0.expr(0)));
    assert_eq!(parse("1"), Ok(1.expr(0)));
    assert_eq!(parse("1  "), Ok(1.expr(0)));
    assert_eq!(parse("9223372036854775807"), Ok(9223372036854775807i64.expr(0..19)));
    assert_eq!(parse("9223372036854776000"), Ok(Object::bigint("9223372036854776000").unwrap().expr(0..19)));
}

#[test]
fn floats() {
    assert_eq!(parse("0.0"), Ok(0f64.expr(0..3)));
    assert_eq!(parse("0."), Ok(0f64.expr(0..2)));
    assert_eq!(parse(".0"), Ok(0f64.expr(0..2)));
    assert_eq!(parse("0e0"), Ok(0f64.expr(0..3)));
    assert_eq!(parse("0e1"), Ok(0f64.expr(0..3)));
    assert_eq!(parse("1."), Ok(1f64.expr(0..2)));
    assert_eq!(parse("1e+1"), Ok(10f64.expr(0..4)));
    assert_eq!(parse("1e1"), Ok(10f64.expr(0..3)));
    assert_eq!(parse("1e-1"), Ok(0.1f64.expr(0..4)));
}

#[test]
fn strings() {
    assert_eq!(parse("\"\""), Ok("".expr(0..2)));
    assert_eq!(parse("\"dingbob\""), Ok("dingbob".expr(0..9)));
    assert_eq!(parse("\"ding\\\"bob\""), Ok("ding\"bob".expr(0..11)));
    assert_eq!(parse("\"ding\\\\bob\""), Ok("ding\\bob".expr(0..11)));

    assert_eq!(
        parse("\"dingbob${a}\""),
        Ok(Expr::String(vec![
            StringElement::raw("dingbob"),
            StringElement::Interpolate("a".id(10)),
        ]).tag(0..13)),
    );

    assert_eq!(
        parse("\"dingbob${ a}\""),
        Ok(Expr::String(vec![
            StringElement::raw("dingbob"),
            StringElement::Interpolate("a".id(11)),
        ]).tag(0..14)),
    );

    assert_eq!(
        parse("\"alpha\" \"bravo\""),
        Ok(Expr::String(vec![
            StringElement::raw("alpha"),
            StringElement::raw("bravo"),
        ]).tag(0..15))
    );
}

#[test]
fn identifiers() {
    assert_eq!(parse("dingbob"), Ok("dingbob".id(0..7)));
    assert_eq!(parse("lets"), Ok("lets".id(0..4)));
    assert_eq!(parse("not1"), Ok("not1".id(0..4)));
}

#[test]
fn lists() {
    assert_eq!(
        parse("[]"),
        Ok(Expr::list(()).tag(0..2)),
    );

    assert_eq!(
        parse("[   ]"),
        Ok(Expr::list(()).tag(0..5)),
    );

    assert_eq!(
        parse("[true]"),
        Ok(Expr::list((
            true.lel(1..5),
        )).tag(0..6)),
    );

    assert_eq!(
        parse("[\"\"]"),
        Ok(Expr::list((
            "".lel(1..3),
        )).tag(0..4)),
    );

    assert_eq!(
        parse("[1,]"),
        Ok(Expr::list((
            1.lel(1),
        )).tag(0..4)),
    );

    assert_eq!(
        parse("[  1   ,  ]"),
        Ok(Expr::list((
            1.lel(3),
        )).tag(0..11)),
    );

    assert_eq!(
        parse("[  1   ,2  ]"),
        Ok(Expr::list((
            1.lel(3),
            2.lel(8),
        )).tag(0..12)),
    );

    assert_eq!(
        parse("[  1   ,2  ,]"),
        Ok(Expr::list((
            1.lel(3),
            2.lel(8),
        )).tag(0..13)),
    );

    assert_eq!(
        parse("[1, false, 2.3, \"fable\", lel]"),
        Ok(Expr::list((
            1.lel(1),
            false.lel(4..9),
            2.3.lel(11..14),
            "fable".lel(16..23),
            ListElement::Singleton("lel".id(25..28)).tag(25..28),
        )).tag(0..29)),
    );

    assert_eq!(
        parse("[1, ...x, y]"),
        Ok(Expr::list((
            1.lel(1),
            "x".id(7).wrap(ListElement::Splat, 4..8),
            "y".id(10).wraptag(ListElement::Singleton),
        )).tag(0..12)),
    );

    assert_eq!(
        parse("[1, for x in y: x, 2]"),
        Ok(Expr::list((
            1.lel(1),
            ListElement::Loop {
                binding: "x".bid(8),
                iterable: "y".id(13),
                element: "x".id(16).wraptag(ListElement::Singleton).to_box(),
            }.tag(4..17),
            2.lel(19),
        )).tag(0..21)),
    );

    assert_eq!(
        parse("[when f(x): x]"),
        Ok(Expr::list((
            ListElement::Cond {
                condition: "f".id(6).funcall((
                    "x".id(8).wraptag(ArgElement::Singleton),
                )).tag(6..10),
                element: "x".id(12).wraptag(ListElement::Singleton).to_box(),
            }.tag(1..13),
        )).tag(0..14)),
    );

    assert_eq!(
        parse("[ 1 , ... x , when x : y , for x in y : z , ]"),
        Ok(Expr::list((
            1.lel(2),
            "x".id(10).wrap(ListElement::Splat, (6, 1, 5)),
            ListElement::Cond {
                condition: "x".id(19),
                element: "y".id(23).wraptag(ListElement::Singleton).to_box(),
            }.tag(14..24),
            ListElement::Loop {
                binding: "x".bid(31),
                iterable: "y".id(36),
                element: "z".id(40).wraptag(ListElement::Singleton).to_box(),
            }.tag(27..41),
        )).tag(0..45)),
    );

    assert_eq!(
        parse("[ (1) , ... (x), when x: (y) , for x in y: (z) ]"),
        Ok(Expr::list((
            1.lel(3),
            "x".id(13).wrap(ListElement::Splat, 8..15),
            ListElement::Cond {
                condition: "x".id(22),
                element: "y".id(26).wraptag(ListElement::Singleton).to_box(),
            }.tag((17, 1, 11)),
            ListElement::Loop {
                binding: "x".bid(35),
                iterable: "y".id(40),
                element: "z".id(44).wraptag(ListElement::Singleton).to_box(),
            }.tag(31..46),
        )).tag(0..48)),
    );
}

#[test]
fn nested_lists() {
    assert_eq!(
        parse("[[]]"),
        Ok(Expr::list((
            Expr::list(()).tag(1..3).wraptag(ListElement::Singleton),
        )).tag(0..4)),
    );

    assert_eq!(
        parse("[1, [2]]"),
        Ok(Expr::list((
            1.lel(1),
            Expr::list((
                2.lel(5),
            )).tag(4..7).wraptag(ListElement::Singleton),
        )).tag(0..8)),
    );
}

#[test]
fn maps() {
    assert_eq!(
        parse("{}"),
        Ok(Expr::map(()).tag(0..2)),
    );

    assert_eq!(
        parse("{  }"),
        Ok(Expr::map(()).tag(0..4)),
    );

    assert_eq!(
        parse("{a: 1}"),
        Ok(Expr::map((
            ("a".lit(1), 1.expr(4)).mel(),
        )).tag(0..6)),
    );

    assert_eq!(
        parse("{a: 1,}"),
        Ok(Expr::map((
            ("a".lit(1), 1.expr(4)).mel(),
        )).tag(0..7)),
    );

    assert_eq!(
        parse("{  a :1,}"),
        Ok(Expr::map((
            ("a".lit(3), 1.expr(6)).mel(),
        )).tag(0..9)),
    );

    assert_eq!(
        parse("{a: 1  ,b:2}"),
        Ok(Expr::map((
            ("a".lit(1), 1.expr(4)).mel(),
            ("b".lit(8), 2.expr(10)).mel(),
        )).tag(0..12)),
    );

    assert_eq!(
        parse("{che9: false}"),
        Ok(Expr::map((
            ("che9".lit(1..5), false.expr(7..12)).mel(),
        )).tag(0..13)),
    );

    assert_eq!(
        parse("{fable: \"fable\"}"),
        Ok(Expr::map((
            ("fable".lit(1..6), "fable".expr(8..15)).mel(),
        )).tag(0..16)),
    );

    assert_eq!(
        parse("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: 1e1}"),
        Ok(Expr::map((
            ("a".lit(1), 1.expr(4)).mel(),
            ("b".lit(7), true.expr(10..14)).mel(),
            ("c".lit(16), 20.0.expr(19..23)).mel(),
            ("d".lit(25), "hoho".expr(28..34)).mel(),
            ("e".lit(36), 10.0.expr(39..42)).mel(),
        )).tag(0..43)),
    );

    assert_eq!(
        parse("{ident-with-hyphen: 1}"),
        Ok(Expr::map((
            ("ident-with-hyphen".lit(1..18), 1.expr(20)).mel(),
        )).tag(0..22)),
    );

    assert_eq!(
        parse("{$z: y}"),
        Ok(Expr::map((
            MapElement::Singleton {
                key: "z".id(2),
                value: "y".id(5)
            }.tag(1..6),
        )).tag(0..7)),
    );

    assert_eq!(
        parse("{$(z): y}"),
        Ok(Expr::map((
            MapElement::Singleton {
                key: "z".id(3),
                value: "y".id(7),
            }.tag(1..8),
        )).tag(0..9)),
    );

    assert_eq!(
        parse("{...y, x: 1}"),
        Ok(Expr::map((
            MapElement::Splat("y".id(4)).tag(1..5),
            ("x".lit(7), 1.expr(10)).mel(),
        )).tag(0..12)),
    );

    assert_eq!(
        parse("{for [x,y] in z: x: y}"),
        Ok(Expr::map((
            MapElement::Loop {
                binding: Binding::List(ListBinding(vec![
                    ListBindingElement::Binding {
                        binding: "x".bid(6),
                        default: None
                    }.tag(6),
                    ListBindingElement::Binding {
                        binding: "y".bid(8),
                        default: None
                    }.tag(8),
                ]).tag(5..10)).tag(5..10),
                iterable: "z".id(14),
                element: ("x".lit(17), "y".id(20)).mel().to_box(),
            }.tag(1..21),
        )).tag(0..22)),
    );

    assert_eq!(
        parse("{when f(x): z: y}"),
        Ok(Expr::map((
            MapElement::Cond {
                condition: "f".id(6).funcall((
                    ArgElement::Singleton("x".id(8)).tag(8),
                )).tag(6..10),
                element: ("z".lit(12), "y".id(15)).mel().to_box(),
            }.tag(1..16),
        )).tag(0..17)),
    );

    assert_eq!(
        parse("{ a : 1 , ... x , when x : b : y , for x in y : c : z , $ f : 2 , }"),
        Ok(Expr::map((
            ("a".lit(2), 1.expr(6)).mel(),
            MapElement::Splat("x".id(14)).tag(10..15),
            MapElement::Cond {
                condition: "x".id(23),
                element: ("b".lit(27), "y".id(31)).mel().to_box(),
            }.tag((18, 1, 14)),
            MapElement::Loop {
                binding: "x".bid(39),
                iterable: "y".id(44),
                element: ("c".lit(48), "z".id(52)).mel().to_box(),
            }.tag(35..53),
            MapElement::Singleton {
                key: "f".id(58),
                value: 2.expr(62)
            }.tag(56..63),
        )).tag(0..67)),
    );

    assert_eq!(
        parse("{ a : (1), ... (x), when x : b : (y), for x in y : c : (z), $ f : (2) }"),
        Ok(Expr::map((
            MapElement::Singleton {
                key: "a".lit(2),
                value: 1.expr(7)
            }.tag(2..9),
            MapElement::Splat("x".id(16)).tag(11..18),
            MapElement::Cond {
                condition: "x".id(25),
                element: MapElement::Singleton {
                    key: "b".lit(29),
                    value: "y".id(34)
                }.tag(29..36).to_box(),
            }.tag(20..36),
            MapElement::Loop {
                binding: "x".bid(42),
                iterable: "y".id(47),
                element: MapElement::Singleton {
                    key: "c".lit(51),
                    value: "z".id(56)
                }.tag(51..58).to_box(),
            }.tag(38..58),
            MapElement::Singleton {
                key: "f".id(62),
                value: 2.expr(67)
            }.tag(60..69),
        )).tag(0..71)),
    );
}

#[test]
fn let_blocks() {
    assert_eq!(
        parse("let a = \"b\" in 1"),
        Ok(Expr::Let {
            bindings: vec![
                ("a".bid(4), "b".expr(8..11)),
            ],
            expression: 1.expr(15).to_box(),
        }.tag(0..16)),
    );

    assert_eq!(
        parse("let a = 1 let b = 2 in a"),
        Ok(Expr::Let {
            bindings: vec![
                ("a".bid(4), 1.expr(8)),
                ("b".bid(14), 2.expr(18)),
            ],
            expression: "a".id(23).to_box(),
        }.tag(0..24)),
    );

    assert_eq!(
        parse("let [a, b=1, ...] = c in [a, b]"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::Binding {
                            binding: "a".bid(5),
                            default: None
                        }.tag(5),
                        ListBindingElement::Binding {
                            binding: "b".bid(8),
                            default: Some(1.expr(10))
                        }.tag(8..11),
                        ListBindingElement::Slurp.tag(13..16),
                    ]).tag(4..17)).tag(4..17),
                    "c".id(20),
                ),
            ],
            expression: Box::new(Expr::list((
                "a".id(26).wraptag(ListElement::Singleton),
                "b".id(29).wraptag(ListElement::Singleton),
            )).tag(25..31)),
        }.tag(0..31)),
    );

    assert_eq!(
        parse("let [_, ...rest] = list in rest"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::Binding {
                            binding: "_".bid(5),
                            default: None
                        }.tag(5),
                        ListBindingElement::SlurpTo("rest".key(11..15)).tag(8..15),
                    ]).tag(4..16)).tag(4..16),
                    "list".id(19..23),
                ),
            ],
            expression: "rest".id(27..31).to_box(),
        }.tag(0..31)),
    );

    assert_eq!(
        parse("let [...a] = b in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::SlurpTo("a".key(8)).tag(5..9),
                    ]).tag(4..10)).tag(4..10),
                    "b".id(13),
                ),
            ],
            expression: "a".id(18).to_box(),
        }.tag(0..19)),
    );

    assert_eq!(
        parse("let [...a,] = b in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::SlurpTo("a".key(8)).tag(5..9),
                    ]).tag(4..11)).tag(4..11),
                    "b".id(14),
                ),
            ],
            expression: "a".id(19).to_box(),
        }.tag(0..20)),
    );

    assert_eq!(
        parse("let {a} = x in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::Map(MapBinding(vec![
                        MapBindingElement::Binding {
                            key: "a".key(5),
                            binding: "a".bid(5),
                            default: None,
                        }.tag(5),
                    ]).tag(4..7)).tag(4..7),
                    "x".id(10),
                ),
            ],
            expression: "a".id(15).to_box(),
        }.tag(0..16)),
    );

    assert_eq!(
        parse("let {a as b} = x in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::Map(MapBinding(vec![
                        MapBindingElement::Binding {
                            key: "a".key(5),
                            binding: "b".bid(10),
                            default: None,
                        }.tag(5..11),
                    ]).tag(4..12)).tag(4..12),
                    "x".id(15),
                ),
            ],
            expression: "a".id(20).to_box(),
        }.tag(0..21)),
    );

    assert_eq!(
        parse("let {a = y} = x in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::Map(MapBinding(vec![
                        MapBindingElement::Binding {
                            key: "a".key(5),
                            binding: "a".bid(5),
                            default: Some("y".id(9)),
                        }.tag(5..10),
                    ]).tag(4..11)).tag(4..11),
                    "x".id(14),
                ),
            ],
            expression: "a".id(19).to_box(),
        }.tag(0..20)),
    );

    assert_eq!(
        parse("let {a as b = y} = x in a"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::Map(MapBinding(vec![
                        MapBindingElement::Binding {
                            key: "a".key(5),
                            binding: "b".bid(10),
                            default: Some("y".id(14)),
                        }.tag(5..15),
                    ]).tag(4..16)).tag(4..16),
                    "x".id(19),
                ),
            ],
            expression: "a".id(24).to_box(),
        }.tag(0..25)),
    );

    assert_eq!(
        parse("let [ y = (1) ] = x in y"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::List(ListBinding(vec![
                        ListBindingElement::Binding {
                            binding: "y".bid(6),
                            default: Some(1.expr(11)),
                        }.tag(6..13),
                    ]).tag(4..15)).tag(4..15),
                    "x".id(18),
                ),
            ],
            expression: "y".id(23).to_box(),
        }.tag(0..24))
    );

    assert_eq!(
        parse("let { y = (1) } = x in y"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Binding::Map(MapBinding(vec![
                        MapBindingElement::Binding {
                            key: "y".key(6),
                            binding: "y".bid(6),
                            default: Some(1.expr(11)),
                        }.tag(6..13),
                    ]).tag(4..15)).tag(4..15),
                    "x".id(18),
                ),
            ],
            expression: "y".id(23).to_box(),
        }.tag(0..24))
    );
}

#[test]
fn branching() {
    assert_eq!(
        parse("if a then b else c"),
        Ok(Expr::Branch {
            condition: "a".id(3).to_box(),
            true_branch: "b".id(10).to_box(),
            false_branch: "c".id(17).to_box(),
        }.tag(0..18)),
    );
}

#[test]
fn indexing() {
    assert_eq!{
        parse("a.b"),
        Ok(
            "a".id(0)
            .index("b".lit(2), 1).tag(0..3)
        ),
    };

    assert_eq!(
        parse("a[b]"),
        Ok(
            "a".id(0)
            .index("b".id(2), 1..4).tag(0..4)
        ),
    );

    assert_eq!(
        parse("a.b.c"),
        Ok(
            "a".id(0)
            .index("b".lit(2), 1).tag(0..3)
            .index("c".lit(4), 3).tag(0..5)
        ),
    );

    assert_eq!(
        parse("a[b].c"),
        Ok(
            "a".id(0)
            .index("b".id(2), 1..4).tag(0..4)
            .index("c".lit(5), 4).tag(0..6)
        ),
    );

    assert_eq!(
        parse("a.b[c]"),
        Ok(
            "a".id(0)
            .index("b".lit(2), 1).tag(0..3)
            .index("c".id(4), 3..6).tag(0..6)
        ),
    );

    assert_eq!(
        parse("a[b][c]"),
        Ok(
            "a".id(0)
            .index("b".id(2), 1..4).tag(0..4)
            .index("c".id(5), 4..7).tag(0..7)
        ),
    );
}

#[test]
fn funcall() {
    assert_eq!(
        parse("func(1, 2, 3,)"),
        Ok("func".id(0..4).funcall((
            1.expr(5).wraptag(ArgElement::Singleton),
            2.expr(8).wraptag(ArgElement::Singleton),
            3.expr(11).wraptag(ArgElement::Singleton),
        )).tag(0..14)),
    );

    assert_eq!(
        parse("func(1, 2, a: 3)"),
        Ok("func".id(0..4).funcall((
            1.expr(5).wraptag(ArgElement::Singleton),
            2.expr(8).wraptag(ArgElement::Singleton),
            ArgElement::Keyword(
                "a".key(11),
                3.expr(14),
            ).tag(11..15),
        )).tag(0..16)),
    );

    assert_eq!(
        parse("func(a: 2, b: 3)"),
        Ok("func".id(0..4).funcall((
            ArgElement::Keyword(
                "a".key(5),
                2.expr(8),
            ).tag(5..9),
            ArgElement::Keyword(
                "b".key(11),
                3.expr(14),
            ).tag(11..15),
        )).tag(0..16)),
    );

    assert_eq!(
        parse("(fn (x,y) => x+y)(1,2)"),
        Ok(
            Expr::Function {
                positional: ListBinding(vec![
                    ListBindingElement::Binding {
                        binding: "x".bid(5),
                        default: None
                    }.tag(5),
                    ListBindingElement::Binding {
                        binding: "y".bid(7),
                        default: None
                    }.tag(7),
                ]),
                keywords: None,
                expression: "x".id(13).add("y".id(15), 14).tag(13..16).to_box(),
            }.tag(1..16).funcall((
                1.expr(18).wraptag(ArgElement::Singleton),
                2.expr(20).wraptag(ArgElement::Singleton),
            )).tag(0..22)
        ),
    );

    assert_eq!(
        parse("func(1, ...y, z: 2, ...q)"),
        Ok("func".id(0..4).funcall((
            1.expr(5).wraptag(ArgElement::Singleton),
            ArgElement::Splat("y".id(11)).tag(8..12),
            ArgElement::Keyword(
                "z".key(14),
                2.expr(17),
            ).tag(14..18),
            ArgElement::Splat("q".id(23)).tag(20..24),
        )).tag(0..25)),
    );
}

#[test]
fn unary_operators() {
    assert_eq!(
        parse("-1"),
        Ok(1.expr(1).neg(0).tag(0..2)),
    );

    assert_eq!(
        parse("- not 1"),
        Ok(1.expr(6).not(2..5).tag(2..7).neg(0).tag(0..7)),
    );

    assert_eq!(
        parse("not -1"),
        Ok(1.expr(5).neg(4).tag(4..6).not(0..3).tag(0..6)),
    );
}

#[test]
fn power_operators() {
    assert_eq!(
        parse("2^3"),
        Ok(
            2.expr(0)
            .pow(3.expr(2), 1).tag(0..3)
        ),
    );

    assert_eq!(
        parse("2^-3"),
        Ok(
            2.expr(0)
            .pow(
                3.expr(3)
                .neg(2).tag(2..4),
                1,
            ).tag(0..4)
        ),
    );

    assert_eq!(
        parse("-2^3"),
        Ok(
            2.expr(1)
            .pow(3.expr(3), 2).tag(1..4)
            .neg(0).tag(0..4)
        ),
    );

    assert_eq!(
        parse("-2^-3"),
        Ok(
            2.expr(1)
            .pow(
                3.expr(4)
                .neg(3).tag(3..5),
                2..3,
            ).tag(1..5)
            .neg(0).tag(0..5)
        ),
    );
}

#[test]
fn operators() {
    assert_eq!(
        parse("1 + 2"),
        Ok(
            1.expr(0)
            .add(2.expr(4), 2).tag(0..5)
        ),
    );

    assert_eq!(
        parse("1 / 2 + 3"),
        Ok(
            1.expr(0)
            .div(2.expr(4), 2).tag(0..5)
            .add(3.expr(8), 6).tag(0..9)
        ),
    );

    assert_eq!(
        parse("1 + 2 - 3 * 4 // 5 / 6"),
        Ok(
            1.expr(0)
            .add(2.expr(4), 2).tag(0..5)
            .sub(
                3.expr(8)
                .mul(4.expr(12), 10).tag(8..13)
                .idiv(5.expr(17), 14..16).tag(8..18)
                .div(6.expr(21), 19).tag(8..22),
                6,
            ).tag(0..22)
        ),
    );

    assert_eq!(
        parse("1 < 2"),
        Ok(
            1.expr(0)
            .lt(2.expr(4), 2).tag(0..5)
        ),
    );

    assert_eq!(
        parse("1 > 2 <= 3 >= 4 == 5 != 6"),
        Ok(
            1.expr(0)
            .gt(2.expr(4), 2).tag(0..5)
            .lte(3.expr(9), 6..8).tag(0..10)
            .gte(4.expr(14), 11..13).tag(0..15)
            .eql(5.expr(19), 16..18).tag(0..20)
            .neql(6.expr(24), 21..23).tag(0..25)
        ),
    );

    assert_eq!(
        parse("1 and 2 or 3"),
        Ok(
            1.expr(0)
            .and(2.expr(6), 2..5).tag(0..7)
            .or(3.expr(11), 8..10).tag(0..12)
        ),
    );

    assert_eq!(
        parse("2 // 2 * 2"),
        Ok(
            2.expr(0)
            .idiv(2.expr(5), 2..4).tag(0..6)
            .mul(2.expr(9), 7..8).tag(0..10)
        ),
    );

    assert_eq!(
        parse("2 ^ 2 ^ 2"),
        Ok(
            2.expr(0)
            .pow(
                2.expr(4)
                .pow(2.expr(8), 6).tag(4..9),
                2,
            ).tag(0..9)
        ),
    );

    assert_eq!(
        parse("-2 ^ 2 ^ 2"),
        Ok(
            2.expr(1)
            .pow(
                2.expr(5)
                .pow(2.expr(9), 7).tag(5..10),
                3,
            ).tag((1, 1, 9))
            .neg(0).tag(0..10)
        ),
    );

    assert_eq!(
        parse("(1 + 2) * 5"),
        Ok(
            1.expr(1)
            .add(2.expr(5), 3).tag(1..6)
            .mul(5.expr(10), 8).tag(0..11)
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
            expression: 1.expr(9).to_box(),
        }.tag(0..10)),
    );

    assert_eq!(
        parse("fn (;) => 1"),
        Ok(Expr::Function {
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![])),
            expression: 1.expr(10).to_box(),
        }.tag(0..11)),
    );

    assert_eq!(
        parse("fn {} => 1"),
        Ok(Expr::Function {
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![])),
            expression: 1.expr(9).to_box(),
        }.tag(0..10)),
    );

    assert_eq!(
        parse("fn (a) => let b = a in b"),
        Ok(Expr::Function {
            positional: ListBinding(vec![
                ListBindingElement::Binding {
                    binding: "a".bid(4),
                    default: None
                }.tag(4),
            ]),
            keywords: None,
            expression: Box::new(Expr::Let {
                bindings: vec![
                    (
                        "b".bid(14),
                        "a".id(18),
                    ),
                ],
                expression: "b".id(23).to_box(),
            }.tag(10..24)),
        }.tag(0..24)),
    );

    assert_eq!(
        parse("fn {x=1, y=2} => x + y"),
        Ok(Expr::Function {
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![
                MapBindingElement::Binding {
                    key: "x".key(4),
                    binding: "x".bid(4),
                    default: Some(1.expr(6)),
                }.tag(4..7),
                MapBindingElement::Binding {
                    key: "y".key(9),
                    binding: "y".bid(9),
                    default: Some(2.expr(11)),
                }.tag(9..12),
            ])),
            expression: "x".id(17).add("y".id(21), 19).tag(17..22).to_box(),
        }.tag(0..22)),
    );
}


macro_rules! syntax_element {
    ($elt:ident) => { SyntaxElement::$elt };
    ($elta:ident, $eltb:ident) => { (SyntaxElement::$elta, SyntaxElement::$eltb) };
    ($elta:ident, $eltb:ident, $eltc:ident) => { (SyntaxElement::$elta, SyntaxElement::$eltb, SyntaxElement::$eltc) };
}


macro_rules! err {
    ($code:expr, $offset:expr, $elt:ident $(,$elts:ident)*) => {
        assert_eq!(
            parse($code),
            Err(Error {
                locations: Some(vec![(Location::new($offset, 1, 0), Action::Parse)]),
                reason: Some(ErrorReason::Syntax(SyntaxErrorReason::from(syntax_element!($elt $(,$elts)*)))),
            })
        )
    };
}


#[test]
fn errors() {
    err!("let", 3, Binding);
    err!("let a", 5, Equals);
    err!("let a =", 7, Expression);
    err!("let a = 1", 9, In);
    err!("let a = 1 in", 12, Expression);

    err!("if", 2, Expression);
    err!("if true", 7, Then);
    err!("if true then", 12, Expression);
    err!("if true then 1", 14, Else);
    err!("if true then 1 else", 19, Expression);

    err!("[", 1, CloseBracket, ListElement);
    err!("[1", 2, CloseBracket, Comma);
    err!("[1,", 3, CloseBracket, ListElement);
    err!("[...", 4, Expression);
    err!("[when", 5, Expression);
    err!("[when x", 7, Colon);
    err!("[when x:", 8, ListElement);
    err!("[when x: 1", 10, CloseBracket, Comma);
    err!("[for", 4, Binding);
    err!("[for x", 6, In);
    err!("[for x in", 9, Expression);
    err!("[for x in y", 11, Colon);
    err!("[for x in y:", 12, ListElement);
    err!("[for x in y: z", 14, CloseBracket, Comma);

    err!("{", 1, CloseBrace, MapElement);
    err!("{x", 2, Colon);
    err!("{x:", 3, Expression);
    err!("{x: y", 5, CloseBrace, Comma);
    err!("{x: y,", 6, CloseBrace, MapElement);
    err!("{$", 2, Expression);
    err!("{$x", 3, Colon);
    err!("{$x:", 4, Expression);
    err!("{$x: y", 6, CloseBrace, Comma);
    err!("{$x: y,", 7, CloseBrace, MapElement);
    err!("{...", 4, Expression);
    err!("{when", 5, Expression);
    err!("{when x", 7, Colon);
    err!("{when x:", 8, MapElement);
    err!("{when x: y", 10, Colon);
    err!("{when x: y:", 11, Expression);
    err!("{when x: y: 1", 13, CloseBrace, Comma);
    err!("{for", 4, Binding);
    err!("{for x", 6, In);
    err!("{for x in", 9, Expression);
    err!("{for x in y", 11, Colon);
    err!("{for x in y:", 12, MapElement);
    err!("{for x in y: z", 14, Colon);
    err!("{for x in y: z:", 15, Expression);
    err!("{for x in y: z: v", 17, CloseBrace, Comma);

    err!("let", 3, Binding);
    err!("let [", 5, CloseBracket, ListBindingElement);
    err!("let [x", 6, CloseBracket, Comma);
    err!("let [x,", 7, CloseBracket, ListBindingElement);
    err!("let [x =", 8, Expression);
    err!("let [x = 1", 10, CloseBracket, Comma);
    err!("let [...", 8, CloseBracket, Comma);
    err!("let {", 5, CloseBrace, MapBindingElement);
    err!("let {y", 6, CloseBrace, Comma);
    err!("let {y,", 7, CloseBrace, MapBindingElement);
    err!("let {y =", 8, Expression);
    err!("let {y = 1", 10, CloseBrace, Comma);
    err!("let {y as", 9, Binding);
    err!("let {y as x =", 13, Expression);
    err!("let {...", 8, Identifier);
    err!("let {...x", 9, CloseBrace, Comma);

    err!("(", 1, Expression);
    err!("(1", 2, CloseParen);

    err!("fn", 2, OpenParen, OpenBrace);
    err!("fn (", 4, CloseParen, Semicolon, PosParam);
    err!("fn (x", 5, CloseParen, Semicolon, Comma);
    err!("fn (x,", 6, CloseParen, Semicolon, PosParam);
    err!("fn (;", 5, CloseParen, KeywordParam);
    err!("fn (;y", 6, CloseParen, Comma);
    err!("fn (;y,", 7, CloseParen, KeywordParam);
    err!("fn ()", 5, DoubleArrow);
    err!("fn () =>", 8, Expression);
    err!("fn {", 4, CloseBrace, KeywordParam);
    err!("fn {x", 5, CloseBrace, Comma);
    err!("fn {x,", 6, CloseBrace, KeywordParam);
    err!("fn {}", 5, DoubleArrow);
    err!("fn {} =>", 8, Expression);

    err!("\"alpha", 6, DoubleQuote);
    err!("\"alpha$", 7, OpenBrace);
    err!("\"alpha${", 8, Expression);
    err!("\"alpha${1", 9, CloseBrace);
    err!("\"alpha${1}", 10, DoubleQuote);

    err!("a.", 2, Identifier);
    err!("a[", 2, Expression);
    err!("a[1", 3, CloseBracket);
    err!("a(", 2, CloseParen, ArgElement);
    err!("a(1", 3, CloseParen, Comma);
    err!("a(1,", 4, CloseParen, ArgElement);
    err!("a(x:", 4, Expression);
    err!("a(...", 5, Expression);

    err!("-", 1, Operand);
    err!("1+", 2, Operand);

    err!("import", 6, ImportPath);
    err!("import \"path\"", 13, As);
    err!("import \"path\" as", 16, Binding);
    err!("import \"path\" as y", 18, Expression);
}
