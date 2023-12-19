use crate::ast::*;
use crate::error::{Tagged, Error, Reason, Syntax, SyntaxElement as S, Action};
use crate::lexing::TokenType as T;
use crate::object::{Object, Key};
use crate::parsing::{parse as parse_file, parse_type};
use crate::traits::{Boxable, Taggable, HasSpan};


fn parse_expr(input: &str) -> Result<Tagged<Expr>, Error> {
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


macro_rules! tag {
    ($node:expr , $line:literal $column:literal $start:literal $end:literal) => {
        $node.tag($start..$end).with_coord($line, $column)
    };
    ($node:expr , $line:literal $column:literal $start:literal) => {
        $node.tag($start).with_coord($line, $column)
    };
    ($node:expr , $start:literal $end:literal) => {
        $node.tag($start..$end)
    };
    ($node:expr , $start:literal) => {
        $node.tag($start)
    };
}


macro_rules! strel {
    ($val:literal) => {
        StringElement::raw($val)
    };
    (interpolate $node:tt) => {
        StringElement::Interpolate(e!($node), None)
    };
    (($($t:tt)*)) => { strel!($($t)*) };
}


macro_rules! listel {
    (splat $node:tt) => {
        e!($node).wrap(ListElement::Splat).adjust(-3, 0)
    };
    (splat $node:tt $offset:literal) => {
        e!($node).wrap(ListElement::Splat).adjust($offset, 0)
    };
    (splat $node:tt $offset:literal $roffset:literal) => {
        e!($node).wrap(ListElement::Splat).adjust($offset, $roffset)
    };
    (each $binding:tt $iterable:tt $expr:tt $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(ListElement::Loop {
            binding: binding!($binding),
            iterable: e!($iterable),
            element: Box::new(listel!($expr)),
        }, $($line $column)? $start $($end)?)
    };
    (cond $cond:tt $expr:tt $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(ListElement::Cond {
            condition: e!($cond),
            element: Box::new(listel!($expr)),
        }, $($line $column)? $start $($end)?)
    };
    ($name:ident $($node:tt)*) => {
        e!($name $($node)*).wrap(ListElement::Singleton)
    };
    (($($t:tt)*)) => { listel!($($t)*) };
}


macro_rules! mapel {
    (splat $node:tt) => {
        e!($node).wrap(MapElement::Splat).adjust(-3, 0)
    };
    (each $binding:tt $iterable:tt $expr:tt $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(MapElement::Loop {
            binding: binding!($binding),
            iterable: e!($iterable),
            element: Box::new(mapel!($expr)),
        }, $($line $column)? $start $($end)?)
    };
    ($key:tt $value:tt) => { {
        let key = e!($key);
        let value = e!($value);
        let span = key.span().join(&value);
        MapElement::Singleton { key, value }.tag(span)
    } };
    ($key:tt $value:tt $offset:literal) => { {
        let key = e!($key);
        let value = e!($value);
        let span = key.span().join(&value);
        MapElement::Singleton { key, value }.tag(span).adjust($offset, 0)
    } };
    (($($t:tt)*)) => { mapel!($($t)*) };
}


macro_rules! argel {
    ($name:ident $($node:tt)*) => {
        e!($name $($node)*).wrap(ArgElement::Singleton)
    };
    (($($t:tt)*)) => { argel!($($t)*) };
}


macro_rules! listbindel {
    ($name:ident $($t:tt)*) => { {
        let binding = binding!($name $($t)*);
        let span = binding.span();
        ListPatternElement::Binding { binding, default: None }.tag(span)
    } };
    (($($t:tt)*)) => { listbindel!($($t)*) };
}


macro_rules! binding {
    (name $val:literal $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(Binding {
            pattern: tag!(Pattern::Identifier(
                tag!(Key::new($val), $($line $column)? $start $($end)?)
            ), $($line $column)? $start $($end)?),
            tp: None,
        }, $($line $column)? $start $($end)?)
    };
    (name $val:ident $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(Binding {
            pattern: tag!(Pattern::Identifier(
                tag!(Key::new(stringify!($val)), $($line $column)? $start $($end)?)
            ), $($line $column)? $start $($end)?),
            tp: None,
        }, $($line $column)? $start $($end)?)
    };
    (list $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? => $($val:tt)*) => {
        tag!(Binding {
            pattern: tag!(Pattern::List(tag!(ListBinding(vec![
                $(listbindel!($val)),*
            ]), $($line $column)? $start $($end)?)), $($line $column)? $start $($end)?),
            tp: None,
        }, $($line $column)? $start $($end)?)
    };
    (($($t:tt)*)) => { binding!($($t)*) };
}


macro_rules! e {
    (true $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(Expr::Literal(Object::bool(true)), $($line $column)? $start $($end)?)
    };
    (false $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(Expr::Literal(Object::bool(false)), $($line $column)? $start $($end)?)
    };
    (null $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(Expr::Literal(Object::null()), $($line $column)? $start $($end)?)
    };
    (name $val:literal $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(
            Expr::Identifier(tag!(Key::new($val), $($line $column)? $start $($end)?)),
            $($line $column)? $start $($end)?
        )
    };
    (name $val:ident $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(
            Expr::Identifier(tag!(Key::new(stringify!($val)), $($line $column)? $start $($end)?)),
            $($line $column)? $start $($end)?
        )
    };
    (int $val:literal $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(Expr::Literal(Object::int($val)), $($line $column)? $start $($end)?)
    };
    (big $val:literal $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(Expr::Literal(Object::bigint($val).unwrap()), $($line $column)? $start $($end)?)
    };
    (float $val:literal $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(Expr::Literal(Object::float($val as f64)), $($line $column)? $start $($end)?)
    };
    (str $val:literal $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(Expr::Literal(Object::str($val)), $($line $column)? $start $($end)?)
    };
    (str $val:ident $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? ) => {
        tag!(Expr::Literal(Object::str(stringify!($val))), $($line $column)? $start $($end)?)
    };
    (cat $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? => $($val:tt)*) => {
        tag!(Expr::String(vec![
            $(strel!($val)),*
        ]), $($line $column)? $start $($end)?)
    };
    (list $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? => $($val:tt)*) => {
        tag!(Expr::List(vec![
            $(listel!($val)),*
        ]), $($line $column)? $start $($end)?)
    };
    (map $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? => $($val:tt)*) => {
        tag!(Expr::Map(vec![
            $(mapel!($val)),*
        ]), $($line $column)? $start $($end)?)
    };
    (call $start:literal $(.. $end:literal)? $(: $line:literal : $column:literal)? => $func:tt $($arg:tt)*) => { {
        let args = tag!(vec![ $(argel!($arg)),* ], $($line $column)? $start $($end)?);
        let func = e!($func);
        let span = func.span().join(&args);
        Expr::Transformed {
            operand: Box::new(func),
            transform: Transform::FunCall(args)
        }.tag(span)
    } };
    (($($t:tt)*)) => { e!($($t)*) };
}


macro_rules! oke {
    ($($rest:tt)*) => { Ok(e!($($rest)*)) };
}


#[test]
fn booleans_and_null() {
    assert_eq!(parse_expr("true"), oke!(true 0..4));
    assert_eq!(parse_expr("false"), oke!(false 0..5));
    assert_eq!(parse_expr("null"), oke!(null 0..4));
}

#[test]
fn integers() {
    assert_eq!(parse_expr("0"), oke!(int 0 0));
    assert_eq!(parse_expr("1"), oke!(int 1 0));
    assert_eq!(parse_expr("1  "), oke!(int 1 0));
    assert_eq!(parse_expr("9223372036854775807"), oke!(int 9223372036854775807i64 0..19));
    assert_eq!(parse_expr("9223372036854776000"), oke!(big "9223372036854776000" 0..19));
}

#[test]
fn floats() {
    assert_eq!(parse_expr("0.0"), oke!(float 0 0..3));
    assert_eq!(parse_expr("0."), oke!(float 0 0..2));
    assert_eq!(parse_expr(".0"), oke!(float 0 0..2));
    assert_eq!(parse_expr("0e0"), oke!(float 0 0..3));
    assert_eq!(parse_expr("0e1"), oke!(float 0 0..3));
    assert_eq!(parse_expr("1."), oke!(float 1 0..2));
    assert_eq!(parse_expr("1e+1"), oke!(float 10 0..4));
    assert_eq!(parse_expr("1e1"), oke!(float 10 0..3));
    assert_eq!(parse_expr("1e-1"), oke!(float 0.1 0..4));
}

#[test]
fn strings() {
    assert_eq!(parse_expr("\"\""), oke!(str "" 0..2));
    assert_eq!(parse_expr("\"dingbob\""), oke!(str "dingbob" 0..9));
    assert_eq!(parse_expr("\"ding\\\"bob\""), oke!(str "ding\"bob" 0..11));
    assert_eq!(parse_expr("\"ding\\\\bob\""), oke!(str "ding\\bob" 0..11));

    assert_eq!(
        parse_expr("\"dingbob${a}\""),
        oke!(cat 0..13 => "dingbob" (interpolate (name "a" 10))),
    );

    assert_eq!(
        parse_expr("\"dingbob${ a}\""),
        oke!(cat 0..14 => "dingbob" (interpolate (name "a" 11))),
    );

    assert_eq!(
        parse_expr("\"alpha\" \"bravo\""),
        oke!(cat 0..15 => "alpha" "bravo")
    );
}

#[test]
fn string_format() {
    assert_eq!(
        FormatSpec::default(),
        FormatSpec {
            fill: ' ',
            align: None,
            sign: None,
            alternate: false,
            width: None,
            grouping: None,
            precision: None,
            fmt_type: None,
        }
    );

    assert_eq!(parse_expr("\"${a}\""), Ok(Expr::String(vec![
        StringElement::Interpolate("a".id(3), None),
    ]).tag(0..6)));

    assert_eq!(parse_expr("\"${a:}\""), Ok(Expr::String(vec![
        StringElement::Interpolate(
            "a".id(3),
            Some(Default::default()),
        ),
    ]).tag(0..7)));

    assert_eq!(parse_expr("\"${a: >+30}\""), Ok(Expr::String(vec![
        StringElement::Interpolate(
            "a".id(3),
            Some(FormatSpec {
                align: Some(AlignSpec::String(StringAlignSpec::Right)),
                sign: Some(SignSpec::Plus),
                width: Some(30),
                ..Default::default()
            })
        ),
    ]).tag(0..12)));

    assert_eq!(parse_expr("\"${a:$^#.3}\""), Ok(Expr::String(vec![
        StringElement::Interpolate(
            "a".id(3),
            Some(FormatSpec {
                fill: '$',
                align: Some(AlignSpec::String(StringAlignSpec::Center)),
                alternate: true,
                precision: Some(3),
                ..Default::default()
            })
        ),
    ]).tag(0..12)));

    assert_eq!(parse_expr("\"${a:0,.5s}\""), Ok(Expr::String(vec![
        StringElement::Interpolate(
            "a".id(3),
            Some(FormatSpec {
                fill: '0',
                align: Some(AlignSpec::AfterSign),
                grouping: Some(GroupingSpec::Comma),
                precision: Some(5),
                fmt_type: Some(FormatType::String),
                ..Default::default()
            })
        ),
    ]).tag(0..12)));
}

#[test]
fn identifiers() {
    assert_eq!(parse_expr("dingbob"), oke!(name "dingbob" 0..7));
    assert_eq!(parse_expr("lets"), oke!(name "lets" 0..4));
    assert_eq!(parse_expr("not1"), oke!(name "not1" 0..4));
}

#[test]
fn lists() {
    assert_eq!(
        parse_expr("[]"),
        oke!(list 0..2 =>),
    );

    assert_eq!(
        parse_expr("[   ]"),
        oke!(list 0..5 =>),
    );

    assert_eq!(
        parse_expr("[true]"),
        oke!(list 0..6 => (true 1..5)),
    );

    assert_eq!(
        parse_expr("[\"\"]"),
        oke!(list 0..4 => (str "" 1..3)),
    );

    assert_eq!(
        parse_expr("[1,]"),
        oke!(list 0..4 => (int 1 1)),
    );

    assert_eq!(
        parse_expr("[  1   ,  ]"),
        oke!(list 0..11 => (int 1 3)),
    );

    assert_eq!(
        parse_expr("[  1   ,2  ]"),
        oke!(list 0..12 => (int 1 3) (int 2 8)),
    );

    assert_eq!(
        parse_expr("[  1   ,2  ,]"),
        oke!(list 0..13 => (int 1 3) (int 2 8)),
    );

    assert_eq!(
        parse_expr("[1, false, 2.3, \"fable\", lel]"),
        oke!(list 0..29 =>
            (int 1 1)
            (false 4..9)
            (float 2.3 11..14)
            (str "fable" 16..23)
            (name "lel" 25..28)
        ),
    );

    assert_eq!(
        parse_expr("[1, ...x, y]"),
        oke!(list 0..12 =>
            (int 1 1)
            (splat (name "x" 7))
            (name "y" 10)
        ),
    );

    assert_eq!(
        parse_expr("[1, for x in y: x, 2]"),
        oke!(list 0..21 =>
            (int 1 1)
            (each (name "x" 8) (name "y" 13) (name "x" 16) 4..17)
            (int 2 19)
        ),
    );

    assert_eq!(
        parse_expr("[when f(x): x]"),
        oke!(list 0..14 =>
            (cond
                (call 7..10 => (name "f" 6) (name "x" 8))
                (name "x" 12)
                1..13
            )
        ),
    );

    assert_eq!(
        parse_expr("[ 1 , ... x , when x : y , for x in y : z , ]"),
        oke!(list 0..45 =>
            (int 1 2)
            (splat (name "x" 10) -4)
            (cond (name "x" 19) (name "y" 23) 14..24)
            (each (name "x" 31) (name "y" 36) (name "z" 40) 27..41)
        ),
    );

    assert_eq!(
        parse_expr("[ (1) , ... (x), when x: (y) , for x in y: (z) ]"),
        oke!(list 0..48 =>
            (int 1 3)
            (splat (name "x" 13) -5 1)
            (cond (name "x" 22) (name "y" 26) 17..28)
            (each (name "x" 35) (name "y" 40) (name "z" 44) 31..46)
        ),
    );
}

#[test]
fn nested_lists() {
    assert_eq!(
        parse_expr("[[]]"),
        oke!(list 0..4 => (list 1..3 =>)),
    );

    assert_eq!(
        parse_expr("[1, [2]]"),
        oke!(list 0..8 =>
            (int 1 1)
            (list 4..7 => (int 2 5))
        ),
    );
}

#[test]
fn maps() {
    assert_eq!(
        parse_expr("{}"),
        oke!(map 0..2 =>),
    );

    assert_eq!(
        parse_expr("{  }"),
        oke!(map 0..4 =>),
    );

    assert_eq!(
        parse_expr("{a: 1}"),
        oke!(map 0..6 => ((str a 1) (int 1 4))),
    );

    assert_eq!(
        parse_expr("{a: 1,}"),
        oke!(map 0..7 => ((str a 1) (int 1 4))),
    );

    assert_eq!(
        parse_expr("{  a :1,}"),
        oke!(map 0..9 => ((str a 3) (int 1 6))),
    );

    assert_eq!(
        parse_expr("{a: 1  ,b:2}"),
        oke!(map 0..12 =>
            ((str a 1) (int 1 4))
            ((str b 8) (int 2 10))
        ),
    );

    assert_eq!(
        parse_expr("{che9: false}"),
        oke!(map 0..13 => ((str che9 1..5) (false 7..12))),
    );

    assert_eq!(
        parse_expr("{fable: \"fable\"}"),
        oke!(map 0..16 => ((str fable 1..6) (str fable 8..15))),
    );

    assert_eq!(
        parse_expr("{format: 1}"),
        oke!(map 0..11 => ((str format 1..7) (int 1 9))),
    );

    assert_eq!(
        parse_expr("{a: 1, b: true, c: 2.e1, d: \"hoho\", e: 1e1}"),
        oke!(map 0..43 =>
            ((str a 1) (int 1 4))
            ((str b 7) (true 10..14))
            ((str c 16) (float 20 19..23))
            ((str d 25) (str hoho 28..34))
            ((str e 36) (float 10 39..42))
        ),
    );

    assert_eq!(
        parse_expr("{ident-with-hyphen: 1}"),
        oke!(map 0..22 => ((str "ident-with-hyphen" 1..18) (int 1 20))),
    );

    assert_eq!(
        parse_expr("{$z: y}"),
        oke!(map 0..7 => ((name z 2) (name y 5) -1)),
    );

    assert_eq!(
        parse_expr("{$(z): y}"),
        oke!(map 0..9 => ((name z 3) (name y 7) -2)),
    );

    assert_eq!(
        parse_expr("{\"z\": y}"),
        oke!(map 0..8 => ((str z 1..4) (name y 6))),
    );

    assert_eq!(
        parse_expr(concat!(
            "{\n",
            "   z:: here's some text\n",
            "}\n",
        )),
        oke!(map 0..27 => ((str z 5:1:3) (str "here's some text" 8..26:1:6))),
    );

    assert_eq!(
        parse_expr(concat!(
            "{\n",
            "   z:: here's some\n",
            "       text\n",
            "}\n",
        )),
        oke!(map 0..34 => ((str z 5:1:3) (str "here's some\ntext" 8..33:1:6))),
    );

    assert_eq!(
        parse_expr(concat!(
            "{\n",
            "   z:: here's some\n",
            "     text\n",
            "}\n",
        )),
        oke!(map 0..32 => ((str z 5:1:3) (str "here's some\ntext" 8..31:1:6))),
    );

    assert_eq!(
        parse_expr(concat!(
            "{\n",
            "   z::\n",
            "     here's some\n",
            "     text\n",
            "}\n",
        )),
        oke!(map 0..37 => ((str z 5:1:3) (str "here's some\ntext" 8..36:1:6))),
    );

    assert_eq!(
        parse_expr(concat!(
            "{\n",
            "   z::\n",
            "     here's some\n",
            "       text\n",
            "}\n",
        )),
        oke!(map 0..39 => ((str z 5:1:3) (str "here's some\n  text" 8..38:1:6))),
    );

    assert_eq!(
        parse_expr(concat!(
            "{\n",
            "   z::\n",
            "       here's some\n",
            "     text\n",
            "}\n",
        )),
        oke!(map 0..39 => ((str z 5:1:3) (str "  here's some\ntext" 8..38:1:6))),
    );

    assert_eq!(
        parse_expr(concat!(
            "{\n",
            "    a:: x\n",
            "    b: y,\n",
            "}\n",
        )),
        oke!(map 0..23 =>
            ((str a 6:1:4) (str x 9..12:1:7))
            ((str b 16:2:4) (name y 19:2:7))
        ),
    );

    assert_eq!(
        parse_expr("{...y, x: 1}"),
        oke!(map 0..12 =>
            (splat (name y 4))
            ((str x 7) (int 1 10))
        ),
    );

    assert_eq!(
        parse_expr("{for [x,y] in z: x: y}"),
        oke!(map 0..22 =>
            (each
                (list 5..10 => (name x 6) (name y 8))
                (name z 14)
                ((str x 17) (name y 20))
                1..21)
        ),
    );

    assert_eq!(
        parse_expr("{when f(x): z: y}"),
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
        parse_expr("{ a : 1 , ... x , when x : b : y , for x in y : c : z , $ f : 2 , }"),
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
        parse_expr("{ a : (1), ... (x), when x : b : (y), for x in y : c : (z), $ f : (2) }"),
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
        parse_expr("let a = \"b\" in 1"),
        Ok(Expr::Let {
            bindings: vec![
                ("a".bid(4), "b".expr(8..11)),
            ],
            expression: 1.expr(15).to_box(),
        }.tag(0..16)),
    );

    assert_eq!(
        parse_expr("let a = 1 let b = 2 in a"),
        Ok(Expr::Let {
            bindings: vec![
                ("a".bid(4), 1.expr(8)),
                ("b".bid(14), 2.expr(18)),
            ],
            expression: "a".id(23).to_box(),
        }.tag(0..24)),
    );

    assert_eq!(
        parse_expr("let [a, b=1, ...] = c in [a, b]"),
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
        parse_expr("let [_, ...rest] = list in rest"),
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
        parse_expr("let [...a] = b in a"),
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
        parse_expr("let [...a,] = b in a"),
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
        parse_expr("let {a} = x in a"),
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
        parse_expr("let {a as b} = x in a"),
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
        parse_expr("let {a = y} = x in a"),
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
        parse_expr("let {a as b = y} = x in a"),
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
        parse_expr("let [ y = (1) ] = x in y"),
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
        parse_expr("let { y = (1) } = x in y"),
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
        parse_expr("if a then b else c"),
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
        parse_expr("a.b"),
        Ok(
            "a".id(0)
            .index("b".lit(2), 1).tag(0..3)
        ),
    };

    assert_eq!(
        parse_expr("a[b]"),
        Ok(
            "a".id(0)
            .index("b".id(2), 1..4).tag(0..4)
        ),
    );

    assert_eq!(
        parse_expr("a.b.c"),
        Ok(
            "a".id(0)
            .index("b".lit(2), 1).tag(0..3)
            .index("c".lit(4), 3).tag(0..5)
        ),
    );

    assert_eq!(
        parse_expr("a[b].c"),
        Ok(
            "a".id(0)
            .index("b".id(2), 1..4).tag(0..4)
            .index("c".lit(5), 4).tag(0..6)
        ),
    );

    assert_eq!(
        parse_expr("a.b[c]"),
        Ok(
            "a".id(0)
            .index("b".lit(2), 1).tag(0..3)
            .index("c".id(4), 3..6).tag(0..6)
        ),
    );

    assert_eq!(
        parse_expr("a[b][c]"),
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
        parse_expr("func(1, 2, 3,)"),
        Ok("func".id(0..4).funcall(vec![
            1.expr(5).wrap(ArgElement::Singleton),
            2.expr(8).wrap(ArgElement::Singleton),
            3.expr(11).wrap(ArgElement::Singleton),
        ], 4..14).tag(0..14)),
    );

    assert_eq!(
        parse_expr("func(1, 2, a: 3)"),
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
        parse_expr("func(a: 2, b: 3)"),
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
        parse_expr("(fn (x,y) x+y)(1,2)"),
        Ok(
            Expr::Function {
                type_params: None,
                positional: ListBinding(vec![
                    ListPatternElement::Binding {
                        binding: "x".bid(5),
                        default: None
                    }.tag(5),
                    ListPatternElement::Binding {
                        binding: "y".bid(7),
                        default: None
                    }.tag(7),
                ]),
                keywords: None,
                return_type: None,
                expression: "x".id(10).add("y".id(12), 11).tag(10..13).to_box(),
            }.tag(1..13).funcall(vec![
                1.expr(15).wrap(ArgElement::Singleton),
                2.expr(17).wrap(ArgElement::Singleton),
            ], 14..19).tag(0..19)
        ),
    );

    assert_eq!(
        parse_expr("func(1, ...y, z: 2, ...q)"),
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
        parse_expr("-1"),
        Ok(1.expr(1).neg(0).tag(0..2)),
    );

    assert_eq!(
        parse_expr("- not 1"),
        Ok(1.expr(6).not(2..5).tag(2..7).neg(0).tag(0..7)),
    );

    assert_eq!(
        parse_expr("not -1"),
        Ok(1.expr(5).neg(4).tag(4..6).not(0..3).tag(0..6)),
    );
}

#[test]
fn power_operators() {
    assert_eq!(
        parse_expr("2^3"),
        Ok(
            2.expr(0)
            .pow(3.expr(2), 1).tag(0..3)
        ),
    );

    assert_eq!(
        parse_expr("2^-3"),
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
        parse_expr("-2^3"),
        Ok(
            2.expr(1)
            .pow(3.expr(3), 2).tag(1..4)
            .neg(0).tag(0..4)
        ),
    );

    assert_eq!(
        parse_expr("-2^-3"),
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
        parse_expr("1 + 2"),
        Ok(
            1.expr(0)
            .add(2.expr(4), 2).tag(0..5)
        ),
    );

    assert_eq!(
        parse_expr("1 / 2 + 3"),
        Ok(
            1.expr(0)
            .div(2.expr(4), 2).tag(0..5)
            .add(3.expr(8), 6).tag(0..9)
        ),
    );

    assert_eq!(
        parse_expr("1 + 2 - 3 * 4 // 5 / 6"),
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
        parse_expr("1 < 2"),
        Ok(
            1.expr(0)
            .lt(2.expr(4), 2).tag(0..5)
        ),
    );

    assert_eq!(
        parse_expr("1 > 2 <= 3 >= 4 == 5 != 6"),
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
        parse_expr("1 and 2 or 3"),
        Ok(
            1.expr(0)
            .and(2.expr(6), 2..5).tag(0..7)
            .or(3.expr(11), 8..10).tag(0..12)
        ),
    );

    assert_eq!(
        parse_expr("2 // 2 * 2"),
        Ok(
            2.expr(0)
            .idiv(2.expr(5), 2..4).tag(0..6)
            .mul(2.expr(9), 7..8).tag(0..10)
        ),
    );

    assert_eq!(
        parse_expr("2 ^ 2 ^ 2"),
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
        parse_expr("-2 ^ 2 ^ 2"),
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
        parse_expr("(1 + 2) * 5"),
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
        parse_expr("fn () 1"),
        Ok(Expr::Function {
            type_params: None,
            positional: ListBinding(vec![]),
            keywords: None,
            return_type: None,
            expression: 1.expr(6).to_box(),
        }.tag(0..7)),
    );

    assert_eq!(
        parse_expr("fn (;) 1"),
        Ok(Expr::Function {
            type_params: None,
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![])),
            return_type: None,
            expression: 1.expr(7).to_box(),
        }.tag(0..8)),
    );

    assert_eq!(
        parse_expr("fn {} 1"),
        Ok(Expr::Function {
            type_params: None,
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![])),
            return_type: None,
            expression: 1.expr(6).to_box(),
        }.tag(0..7)),
    );

    assert_eq!(
        parse_expr("fn (a) let b = a in b"),
        Ok(Expr::Function {
            type_params: None,
            positional: ListBinding(vec![
                ListPatternElement::Binding {
                    binding: "a".bid(4),
                    default: None
                }.tag(4),
            ]),
            keywords: None,
            return_type: None,
            expression: Box::new(Expr::Let {
                bindings: vec![
                    (
                        "b".bid(11),
                        "a".id(15),
                    ),
                ],
                expression: "b".id(20).to_box(),
            }.tag(7..21)),
        }.tag(0..21)),
    );

    assert_eq!(
        parse_expr("fn {x=1, y=2} x + y"),
        Ok(Expr::Function {
            type_params: None,
            positional: ListBinding(vec![]),
            keywords: Some(MapBinding(vec![
                MapPatternElement::Binding {
                    key: "x".key(4),
                    binding: "x".bid(4),
                    default: Some(1.expr(6)),
                }.tag(4..7),
                MapPatternElement::Binding {
                    key: "y".key(9),
                    binding: "y".bid(9),
                    default: Some(2.expr(11)),
                }.tag(9..12),
            ])),
            return_type: None,
            expression: "x".id(14).add("y".id(18), 16).tag(14..19).to_box(),
        }.tag(0..19)),
    );
}


#[test]
fn types() {
    assert_eq!(
        parse_type("int"),
        Ok("int".id(0..3)),
    );

    assert_eq!(
        parse_type("list<int>"),
        Ok("list".id(0..4).typecall(vec![
            "int".id(5..8).wrap(ArgElement::Singleton),
        ], 4..9).tag(0..9)),
    );

    assert_eq!(
        parse_type("list<dict<int>>"),
        Ok("list".id(0..4).typecall(vec![
            ArgElement::Singleton("dict".id(5..9).typecall(vec![
                "int".id(10..13).wrap(ArgElement::Singleton),
            ], 9..14).tag(5..14)).tag(5..14)
        ], 4..15).tag(0..15)),
    );

    assert_eq!(
        parse_type("[int, str]"),
        Ok(Expr::list(vec![
            "int".id(1..4).wrap(ListElement::Singleton),
            "str".id(6..9).wrap(ListElement::Singleton),
        ]).tag(0..10)),
    );

    assert_eq!(
        parse_type("[number, list<int>]"),
        Ok(Expr::list(vec![
            "number".id(1..7).wrap(ListElement::Singleton),
            ListElement::Singleton(
                "list".id(9..13).typecall(vec![
                    "int".id(14..17).wrap(ArgElement::Singleton),
                ], 13..18).tag(9..18)
            ).tag(9..18),
        ]).tag(0..19)),
    );

    assert_eq!(
        parse_type("[argh, ...blargh]"),
        Ok(Expr::list(vec![
            "argh".id(1..5).wrap(ListElement::Singleton),
            "blargh".id(10..16).wrap(ListElement::Splat).retag(7..16),
        ]).tag(0..17)),
    );
}


macro_rules! err {
    ($code:expr, $offset:expr, $elt:expr $(,$elts:expr)*) => {
        assert_eq!(
            parse_expr($code),
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
            parse_expr($code),
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

    err!("fn (", 4, T::CloseParen, T::SemiColon, S::PosParam);
    err!("fn (x", 5, T::CloseParen, T::SemiColon, T::Comma);
    err!("fn (x,", 6, T::CloseParen, T::SemiColon, S::PosParam);
    err!("fn (;", 5, T::CloseParen, S::KeywordParam);
    err!("fn (;y", 6, T::CloseParen, T::Comma);
    err!("fn (;y,", 7, T::CloseParen, S::KeywordParam);
    err!("fn ()", 5, S::Expression);
    err!("fn {", 4, T::CloseBrace, S::KeywordParam);
    err!("fn {x", 5, T::CloseBrace, T::Comma);
    err!("fn {x,", 6, T::CloseBrace, S::KeywordParam);
    err!("fn {}", 5, S::Expression);

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
