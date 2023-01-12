use crate::ast::*;
use crate::error::{Tagged, Error, Reason, Syntax, SyntaxElement as S, Action};
use crate::lexing::{TokenType as T};
use crate::object::{Object, Key};
use crate::parsing::{parse as parse_file};
use crate::traits::{Boxable, Taggable, HasSpan};


fn parse(input: &str) -> Result<Tagged<Expr>, Error> {
    parse_file(input).map(|x| x.expression).map_err(Error::unrender)
}

trait IdAble {
    fn id(self, loc: impl HasSpan) -> Tagged<Expr>;
}

impl<U> IdAble for U where U: KeyAble {
    fn id(self, loc: impl HasSpan) -> Tagged<Expr> {
        self.key(loc).wrap(Expr::Identifier)
    }
}

trait LitAble {
    fn lit(self, loc: impl HasSpan) -> Tagged<Expr>;
}

impl<U> LitAble for U where U: KeyAble {
    fn lit(self, loc: impl HasSpan) -> Tagged<Expr> {
        self.key(loc).map(Object::from).map(Expr::Literal)
    }
}

trait BindingIdAble {
    fn bid(self, loc: impl HasSpan) -> Tagged<Binding>;
}

impl<U> BindingIdAble for U where U: KeyAble {
    fn bid(self, loc: impl HasSpan) -> Tagged<Binding> {
        let span = loc.span();
        Binding {
            pattern: Pattern::Identifier(self.key(span)).tag(span),
            tp: None,
        }.tag(span)
    }
}

trait BindingAble {
    fn bind(self) -> Tagged<Binding>;
}

impl BindingAble for Tagged<Pattern> {
    fn bind(self) -> Tagged<Binding> {
        let span = self.span();
        Binding {
            pattern: self,
            tp: None,
        }.tag(span)
    }
}

trait KeyAble {
    fn key(self, loc: impl HasSpan) -> Tagged<Key>;
}

impl<U> KeyAble for U where U: AsRef<str> {
    fn key(self, loc: impl HasSpan) -> Tagged<Key> {
        Key::new(self).tag(loc)
    }
}

trait ListElementAble {
    fn lel(self, loc: impl HasSpan) -> Tagged<ListElement>;
}

impl<U> ListElementAble for U where Object: From<U> {
    fn lel(self, loc: impl HasSpan) -> Tagged<ListElement> {
        Expr::Literal(Object::from(self)).tag(loc).wrap(ListElement::Singleton)
    }
}

trait MapElementAble {
    fn mel(self) -> Tagged<MapElement>;
}

impl MapElementAble for (Tagged<Expr>, Tagged<Expr>) {
    fn mel(self) -> Tagged<MapElement> {
        let loc = self.0.span()..self.1.span();
        MapElement::Singleton {
            key: self.0,
            value: self.1
        }.tag(loc)
    }
}

trait ExprAble {
    fn expr(self, loc: impl HasSpan) -> Tagged<Expr>;
}

impl<U> ExprAble for U where Object: From<U> {
    fn expr(self, loc: impl HasSpan) -> Tagged<Expr> {
        Expr::Literal(Object::from(self)).tag(loc)
    }
}


#[test]
fn booleans_and_null() {
    assert_eq!(parse("true"), Ok(true.expr(0..4)));
    assert_eq!(parse("false"), Ok(false.expr(0..5)));
    assert_eq!(parse("null"), Ok(Object::null().expr(0..4)));
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
        Ok(Expr::list(vec![
            true.lel(1..5),
        ]).tag(0..6)),
    );

    assert_eq!(
        parse("[\"\"]"),
        Ok(Expr::list(vec![
            "".lel(1..3),
        ]).tag(0..4)),
    );

    assert_eq!(
        parse("[1,]"),
        Ok(Expr::list(vec![
            1.lel(1),
        ]).tag(0..4)),
    );

    assert_eq!(
        parse("[  1   ,  ]"),
        Ok(Expr::list(vec![
            1.lel(3),
        ]).tag(0..11)),
    );

    assert_eq!(
        parse("[  1   ,2  ]"),
        Ok(Expr::list(vec![
            1.lel(3),
            2.lel(8),
        ]).tag(0..12)),
    );

    assert_eq!(
        parse("[  1   ,2  ,]"),
        Ok(Expr::list(vec![
            1.lel(3),
            2.lel(8),
        ]).tag(0..13)),
    );

    assert_eq!(
        parse("[1, false, 2.3, \"fable\", lel]"),
        Ok(Expr::list(vec![
            1.lel(1),
            false.lel(4..9),
            2.3.lel(11..14),
            "fable".lel(16..23),
            ListElement::Singleton("lel".id(25..28)).tag(25..28),
        ]).tag(0..29)),
    );

    assert_eq!(
        parse("[1, ...x, y]"),
        Ok(Expr::list(vec![
            1.lel(1),
            "x".id(7).wrap(ListElement::Splat).retag(4..8),
            "y".id(10).wrap(ListElement::Singleton),
        ]).tag(0..12)),
    );

    assert_eq!(
        parse("[1, for x in y: x, 2]"),
        Ok(Expr::list(vec![
            1.lel(1),
            ListElement::Loop {
                binding: "x".bid(8),
                iterable: "y".id(13),
                element: "x".id(16).wrap(ListElement::Singleton).to_box(),
            }.tag(4..17),
            2.lel(19),
        ]).tag(0..21)),
    );

    assert_eq!(
        parse("[when f(x): x]"),
        Ok(Expr::list(vec![
            ListElement::Cond {
                condition: "f".id(6).funcall(vec![
                    "x".id(8).wrap(ArgElement::Singleton),
                ], 7..10).tag(6..10),
                element: "x".id(12).wrap(ListElement::Singleton).to_box(),
            }.tag(1..13),
        ]).tag(0..14)),
    );

    assert_eq!(
        parse("[ 1 , ... x , when x : y , for x in y : z , ]"),
        Ok(Expr::list(vec![
            1.lel(2),
            "x".id(10).wrap(ListElement::Splat).retag(6..11),
            ListElement::Cond {
                condition: "x".id(19),
                element: "y".id(23).wrap(ListElement::Singleton).to_box(),
            }.tag(14..24),
            ListElement::Loop {
                binding: "x".bid(31),
                iterable: "y".id(36),
                element: "z".id(40).wrap(ListElement::Singleton).to_box(),
            }.tag(27..41),
        ]).tag(0..45)),
    );

    assert_eq!(
        parse("[ (1) , ... (x), when x: (y) , for x in y: (z) ]"),
        Ok(Expr::list(vec![
            1.lel(3),
            "x".id(13).wrap(ListElement::Splat).retag(8..15),
            ListElement::Cond {
                condition: "x".id(22),
                element: "y".id(26).wrap(ListElement::Singleton).to_box(),
            }.tag(17..28),
            ListElement::Loop {
                binding: "x".bid(35),
                iterable: "y".id(40),
                element: "z".id(44).wrap(ListElement::Singleton).to_box(),
            }.tag(31..46),
        ]).tag(0..48)),
    );
}

#[test]
fn nested_lists() {
    assert_eq!(
        parse("[[]]"),
        Ok(Expr::list(vec![
            Expr::list(()).tag(1..3).wrap(ListElement::Singleton),
        ]).tag(0..4)),
    );

    assert_eq!(
        parse("[1, [2]]"),
        Ok(Expr::list(vec![
            1.lel(1),
            Expr::list(vec![
                2.lel(5),
            ]).tag(4..7).wrap(ListElement::Singleton),
        ]).tag(0..8)),
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
        Ok(Expr::map(vec![
            ("a".lit(1), 1.expr(4)).mel(),
        ]).tag(0..6)),
    );

    assert_eq!(
        parse("{a: 1,}"),
        Ok(Expr::map(vec![
            ("a".lit(1), 1.expr(4)).mel(),
        ]).tag(0..7)),
    );

    assert_eq!(
        parse("{  a :1,}"),
        Ok(Expr::map(vec![
            ("a".lit(3), 1.expr(6)).mel(),
        ]).tag(0..9)),
    );

    assert_eq!(
        parse("{a: 1  ,b:2}"),
        Ok(Expr::map(vec![
            ("a".lit(1), 1.expr(4)).mel(),
            ("b".lit(8), 2.expr(10)).mel(),
        ]).tag(0..12)),
    );

    assert_eq!(
        parse("{che9: false}"),
        Ok(Expr::map(vec![
            ("che9".lit(1..5), false.expr(7..12)).mel(),
        ]).tag(0..13)),
    );

    assert_eq!(
        parse("{fable: \"fable\"}"),
        Ok(Expr::map(vec![
            ("fable".lit(1..6), "fable".expr(8..15)).mel(),
        ]).tag(0..16)),
    );

    assert_eq!(
        parse("{format: 1}"),
        Ok(Expr::map(vec![
            ("format".lit(1..7), 1.expr(9)).mel(),
        ]).tag(0..11)),
    );

    assert_eq!(
        parse("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: 1e1}"),
        Ok(Expr::map(vec![
            ("a".lit(1), 1.expr(4)).mel(),
            ("b".lit(7), true.expr(10..14)).mel(),
            ("c".lit(16), 20.0.expr(19..23)).mel(),
            ("d".lit(25), "hoho".expr(28..34)).mel(),
            ("e".lit(36), 10.0.expr(39..42)).mel(),
        ]).tag(0..43)),
    );

    assert_eq!(
        parse("{ident-with-hyphen: 1}"),
        Ok(Expr::map(vec![
            ("ident-with-hyphen".lit(1..18), 1.expr(20)).mel(),
        ]).tag(0..22)),
    );

    assert_eq!(
        parse("{$z: y}"),
        Ok(Expr::map(vec![
            MapElement::Singleton {
                key: "z".id(2),
                value: "y".id(5)
            }.tag(1..6),
        ]).tag(0..7)),
    );

    assert_eq!(
        parse("{$(z): y}"),
        Ok(Expr::map(vec![
            MapElement::Singleton {
                key: "z".id(3),
                value: "y".id(7),
            }.tag(1..8),
        ]).tag(0..9)),
    );

    assert_eq!(
        parse("{\"z\": y}"),
        Ok(Expr::map(vec![
            ("z".lit(1..4), "y".id(6)).mel(),
        ]).tag(0..8)),
    );

    assert_eq!(
        parse(concat!(
            "{\n",
            "   z:: here's some text\n",
            "}\n",
        )),
        Ok(Expr::map(vec![
            ("z".lit(5).with_coord(1,3), "here's some text".expr(8..26).with_coord(1,6)).mel(),
        ]).tag(0..27)),
    );

    assert_eq!(
        parse(concat!(
            "{\n",
            "   z:: here's some\n",
            "       text\n",
            "}\n",
        )),
        Ok(Expr::map(vec![
            ("z".lit(5).with_coord(1,3), "here's some\ntext".expr(8..33).with_coord(1,6)).mel(),
        ]).tag(0..34)),
    );

    assert_eq!(
        parse(concat!(
            "{\n",
            "   z:: here's some\n",
            "     text\n",
            "}\n",
        )),
        Ok(Expr::map(vec![
            ("z".lit(5).with_coord(1,3), "here's some\ntext".expr(8..31).with_coord(1,6)).mel(),
        ]).tag(0..32)),
    );

    assert_eq!(
        parse(concat!(
            "{\n",
            "   z::\n",
            "     here's some\n",
            "     text\n",
            "}\n",
        )),
        Ok(Expr::map(vec![
            ("z".lit(5).with_coord(1,3), "here's some\ntext".expr(8..36).with_coord(1,6)).mel(),
        ]).tag(0..37)),
    );

    assert_eq!(
        parse(concat!(
            "{\n",
            "   z::\n",
            "     here's some\n",
            "       text\n",
            "}\n",
        )),
        Ok(Expr::map(vec![
            ("z".lit(5).with_coord(1,3), "here's some\n  text".expr(8..38).with_coord(1,6)).mel(),
        ]).tag(0..39)),
    );

    assert_eq!(
        parse(concat!(
            "{\n",
            "   z::\n",
            "       here's some\n",
            "     text\n",
            "}\n",
        )),
        Ok(Expr::map(vec![
            ("z".lit(5).with_coord(1,3), "  here's some\ntext".expr(8..38).with_coord(1,6)).mel(),
        ]).tag(0..39)),
    );

    assert_eq!(
        parse(concat!(
            "{\n",
            "    a:: x\n",
            "    b: y,\n",
            "}\n",
        )),
        Ok(Expr::map(vec![
            ("a".lit(6).with_coord(1,4), "x".expr(9..12).with_coord(1,7)).mel(),
            ("b".lit(16).with_coord(2,4), "y".key(19).with_coord(2,7).wrap(Expr::Identifier)).mel(),
        ]).tag(0..23)),
    );

    assert_eq!(
        parse("{...y, x: 1}"),
        Ok(Expr::map(vec![
            MapElement::Splat("y".id(4)).tag(1..5),
            ("x".lit(7), 1.expr(10)).mel(),
        ]).tag(0..12)),
    );

    assert_eq!(
        parse("{for [x,y] in z: x: y}"),
        Ok(Expr::map(vec![
            MapElement::Loop {
                binding: Pattern::List(ListBinding(vec![
                    ListPatternElement::Binding {
                        binding: "x".bid(6),
                        default: None
                    }.tag(6),
                    ListPatternElement::Binding {
                        binding: "y".bid(8),
                        default: None
                    }.tag(8),
                ]).tag(5..10)).tag(5..10).bind(),
                iterable: "z".id(14),
                element: ("x".lit(17), "y".id(20)).mel().to_box(),
            }.tag(1..21),
        ]).tag(0..22)),
    );

    assert_eq!(
        parse("{when f(x): z: y}"),
        Ok(Expr::map(vec![
            MapElement::Cond {
                condition: "f".id(6).funcall(vec![
                    ArgElement::Singleton("x".id(8)).tag(8),
                ], 7..10).tag(6..10),
                element: ("z".lit(12), "y".id(15)).mel().to_box(),
            }.tag(1..16),
        ]).tag(0..17)),
    );

    assert_eq!(
        parse("{ a : 1 , ... x , when x : b : y , for x in y : c : z , $ f : 2 , }"),
        Ok(Expr::map(vec![
            ("a".lit(2), 1.expr(6)).mel(),
            MapElement::Splat("x".id(14)).tag(10..15),
            MapElement::Cond {
                condition: "x".id(23),
                element: ("b".lit(27), "y".id(31)).mel().to_box(),
            }.tag(18..32),
            MapElement::Loop {
                binding: "x".bid(39),
                iterable: "y".id(44),
                element: ("c".lit(48), "z".id(52)).mel().to_box(),
            }.tag(35..53),
            MapElement::Singleton {
                key: "f".id(58),
                value: 2.expr(62)
            }.tag(56..63),
        ]).tag(0..67)),
    );

    assert_eq!(
        parse("{ a : (1), ... (x), when x : b : (y), for x in y : c : (z), $ f : (2) }"),
        Ok(Expr::map(vec![
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
        ]).tag(0..71)),
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
                    Pattern::List(ListBinding(vec![
                        ListPatternElement::Binding {
                            binding: "a".bid(5),
                            default: None
                        }.tag(5),
                        ListPatternElement::Binding {
                            binding: "b".bid(8),
                            default: Some(1.expr(10))
                        }.tag(8..11),
                        ListPatternElement::Slurp.tag(13..16),
                    ]).tag(4..17)).tag(4..17).bind(),
                    "c".id(20),
                ),
            ],
            expression: Box::new(Expr::list(vec![
                "a".id(26).wrap(ListElement::Singleton),
                "b".id(29).wrap(ListElement::Singleton),
            ]).tag(25..31)),
        }.tag(0..31)),
    );

    assert_eq!(
        parse("let [_, ...rest] = list in rest"),
        Ok(Expr::Let {
            bindings: vec![
                (
                    Pattern::List(ListBinding(vec![
                        ListPatternElement::Binding {
                            binding: "_".bid(5),
                            default: None
                        }.tag(5),
                        ListPatternElement::SlurpTo("rest".key(11..15)).tag(8..15),
                    ]).tag(4..16)).tag(4..16).bind(),
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
                    Pattern::List(ListBinding(vec![
                        ListPatternElement::SlurpTo("a".key(8)).tag(5..9),
                    ]).tag(4..10)).tag(4..10).bind(),
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
                    Pattern::List(ListBinding(vec![
                        ListPatternElement::SlurpTo("a".key(8)).tag(5..9),
                    ]).tag(4..11)).tag(4..11).bind(),
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
                    Pattern::Map(MapBinding(vec![
                        MapPatternElement::Binding {
                            key: "a".key(5),
                            binding: "a".bid(5),
                            default: None,
                        }.tag(5),
                    ]).tag(4..7)).tag(4..7).bind(),
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
                    Pattern::Map(MapBinding(vec![
                        MapPatternElement::Binding {
                            key: "a".key(5),
                            binding: "b".bid(10),
                            default: None,
                        }.tag(5..11),
                    ]).tag(4..12)).tag(4..12).bind(),
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
                    Pattern::Map(MapBinding(vec![
                        MapPatternElement::Binding {
                            key: "a".key(5),
                            binding: "a".bid(5),
                            default: Some("y".id(9)),
                        }.tag(5..10),
                    ]).tag(4..11)).tag(4..11).bind(),
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
                    Pattern::Map(MapBinding(vec![
                        MapPatternElement::Binding {
                            key: "a".key(5),
                            binding: "b".bid(10),
                            default: Some("y".id(14)),
                        }.tag(5..15),
                    ]).tag(4..16)).tag(4..16).bind(),
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
                    Pattern::List(ListBinding(vec![
                        ListPatternElement::Binding {
                            binding: "y".bid(6),
                            default: Some(1.expr(11)),
                        }.tag(6..13),
                    ]).tag(4..15)).tag(4..15).bind(),
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
                    Pattern::Map(MapBinding(vec![
                        MapPatternElement::Binding {
                            key: "y".key(6),
                            binding: "y".bid(6),
                            default: Some(1.expr(11)),
                        }.tag(6..13),
                    ]).tag(4..15)).tag(4..15).bind(),
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
        Ok("func".id(0..4).funcall(vec![
            1.expr(5).wrap(ArgElement::Singleton),
            2.expr(8).wrap(ArgElement::Singleton),
            3.expr(11).wrap(ArgElement::Singleton),
        ], 4..14).tag(0..14)),
    );

    assert_eq!(
        parse("func(1, 2, a: 3)"),
        Ok("func".id(0..4).funcall(vec![
            1.expr(5).wrap(ArgElement::Singleton),
            2.expr(8).wrap(ArgElement::Singleton),
            ArgElement::Keyword(
                "a".key(11),
                3.expr(14),
            ).tag(11..15),
        ], 4..16).tag(0..16)),
    );

    assert_eq!(
        parse("func(a: 2, b: 3)"),
        Ok("func".id(0..4).funcall(vec![
            ArgElement::Keyword(
                "a".key(5),
                2.expr(8),
            ).tag(5..9),
            ArgElement::Keyword(
                "b".key(11),
                3.expr(14),
            ).tag(11..15),
        ], 4..16).tag(0..16)),
    );

    assert_eq!(
        parse("(|x,y| x+y)(1,2)"),
        Ok(
            Expr::Function {
                type_params: None,
                positional: ListBinding(vec![
                    ListPatternElement::Binding {
                        binding: "x".bid(2),
                        default: None
                    }.tag(2),
                    ListPatternElement::Binding {
                        binding: "y".bid(4),
                        default: None
                    }.tag(4),
                ]),
                keywords: None,
                return_type: None,
                expression: "x".id(7).add("y".id(9), 8).tag(7..10).to_box(),
            }.tag(1..10).funcall(vec![
                1.expr(12).wrap(ArgElement::Singleton),
                2.expr(14).wrap(ArgElement::Singleton),
            ], 11..16).tag(0..16)
        ),
    );

    assert_eq!(
        parse("func(1, ...y, z: 2, ...q)"),
        Ok("func".id(0..4).funcall(vec![
            1.expr(5).wrap(ArgElement::Singleton),
            ArgElement::Splat("y".id(11)).tag(8..12),
            ArgElement::Keyword(
                "z".key(14),
                2.expr(17),
            ).tag(14..18),
            ArgElement::Splat("q".id(23)).tag(20..24),
        ], 4..25).tag(0..25)),
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
            .equal(5.expr(19), 16..18).tag(0..20)
            .not_equal(6.expr(24), 21..23).tag(0..25)
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
            ).tag(1..10)
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
        parse("|| 1"),
        Ok(Expr::Function {
            type_params: None,
            positional: ListBinding(vec![]),
            keywords: None,
            return_type: None,
            expression: 1.expr(3).to_box(),
        }.tag(0..4)),
    );

    assert_eq!(
        parse("|;| 1"),
        Ok(Expr::Function {
            type_params: None,
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![])),
            return_type: None,
            expression: 1.expr(4).to_box(),
        }.tag(0..5)),
    );

    assert_eq!(
        parse("{||} 1"),
        Ok(Expr::Function {
            type_params: None,
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![])),
            return_type: None,
            expression: 1.expr(5).to_box(),
        }.tag(0..6)),
    );

    assert_eq!(
        parse("|a| let b = a in b"),
        Ok(Expr::Function {
            type_params: None,
            positional: ListBinding(vec![
                ListPatternElement::Binding {
                    binding: "a".bid(1),
                    default: None
                }.tag(1),
            ]),
            keywords: None,
            return_type: None,
            expression: Box::new(Expr::Let {
                bindings: vec![
                    (
                        "b".bid(8),
                        "a".id(12),
                    ),
                ],
                expression: "b".id(17).to_box(),
            }.tag(4..18)),
        }.tag(0..18)),
    );

    assert_eq!(
        parse("{|x=1, y=2|} x + y"),
        Ok(Expr::Function {
            type_params: None,
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![
                MapPatternElement::Binding {
                    key: "x".key(2),
                    binding: "x".bid(2),
                    default: Some(1.expr(4)),
                }.tag(2..5),
                MapPatternElement::Binding {
                    key: "y".key(7),
                    binding: "y".bid(7),
                    default: Some(2.expr(9)),
                }.tag(7..10),
            ])),
            return_type: None,
            expression: "x".id(13).add("y".id(17), 15).tag(13..18).to_box(),
        }.tag(0..18)),
    );
}


macro_rules! err {
    ($code:expr, $offset:expr, $elt:expr $(,$elts:expr)*) => {
        assert_eq!(
            parse($code),
            Err(Error {
                locations: Some(vec![(($offset..$offset).span(), Action::Parse)]),
                reason: Some(Reason::Syntax(Syntax::from(($elt $(,$elts)*)))),
                rendered: None,
            })
        )
    };
}


macro_rules! errl {
    ($code:expr, $offset:expr, $elt:expr) => {
        assert_eq!(
            parse($code),
            Err(Error {
                locations: Some(vec![($offset.span(), Action::Parse)]),
                reason: Some(Reason::Syntax($elt)),
                rendered: None,
            })
        )
    };
}


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

    err!("|", 1, T::Pipe, T::SemiColon, S::PosParam);
    err!("|x", 2, T::Pipe, T::SemiColon, T::Comma);
    err!("|x,", 3, T::Pipe, T::SemiColon, S::PosParam);
    err!("|;", 2, T::Pipe, S::KeywordParam);
    err!("|;y", 3, T::Pipe, T::Comma);
    err!("|;y,", 4, T::Pipe, S::KeywordParam);
    err!("||", 2, S::Expression);
    err!("{|", 2, T::CloseBracePipe, S::KeywordParam);
    err!("{|x", 3, T::CloseBracePipe, T::Comma);
    err!("{|x,", 4, T::CloseBracePipe, S::KeywordParam);
    err!("{||}", 4, S::Expression);

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

    errl!("let [x, ..., y, ...] = z in 2", 16..19, Syntax::MultiSlurp);
    errl!("let {x, ...a, y, ...b} = z in 2", 17..21, Syntax::MultiSlurp);
}
