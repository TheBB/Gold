use crate::ast::{BinOp, UnOp};
use crate::error::{Error, Reason, Unpack, Span, Action, BindingType, TypeMismatch};
use crate::eval_raw;
use crate::object::{Object, Key, Type};


fn eval(input: &str) -> Result<Object, Error> {
    eval_raw(input).map_err(Error::unrender)
}

fn eval_errstr(input: &str) -> Option<String> {
    eval_raw(input).err().map(|x| x.rendered).flatten()
}


trait KeyAble {
    fn key(self) -> Key;
}

impl<U> KeyAble for U where U: AsRef<str> {
    fn key(self) -> Key {
        Key::new(self)
    }
}


macro_rules! assert_seq {
    ($x:expr , $y:expr $(,)?) => {
        assert_eq!($x, Ok($y))
    };
}


#[test]
fn booleans_and_null() {
    assert_seq!(eval("true"), Object::from(true));
    assert_seq!(eval("false"), Object::from(false));
    assert_seq!(eval("null"), Object::Null);
}


#[test]
fn integers() {
    assert_seq!(eval("1"), Object::from(1));
    assert_seq!(eval("-1"), Object::from(-1));
    assert_seq!(eval("+1"), Object::from(1));
}


#[test]
fn floats() {
    assert_seq!(eval("2."), Object::from(2.0));
    assert_seq!(eval("1.2"), Object::from(1.2));
    assert_seq!(eval("-3e1"), Object::from(-30.0));
    assert_seq!(eval("+4e-1"), Object::from(0.4));
    assert_seq!(eval("5e+1"), Object::from(50.0));
}


#[test]
fn strings() {
    assert_seq!(eval("\"\""), Object::interned(""));
    assert_seq!(eval("\"simsalabim\""), Object::interned("simsalabim"));
    assert_seq!(eval("\"simsalabim ${-1} abracadabra\""), Object::natural_string("simsalabim -1 abracadabra"));
    assert_seq!(eval("\"simsalabim ${0} abracadabra\""), Object::natural_string("simsalabim 0 abracadabra"));
    assert_seq!(eval("\"simsalabim ${1} abracadabra\""), Object::natural_string("simsalabim 1 abracadabra"));
    assert_seq!(eval("\"simsalabim ${9223372036854775807} abracadabra\""), Object::natural_string("simsalabim 9223372036854775807 abracadabra"));
    assert_seq!(eval("\"simsalabim ${9223372036854776000} abracadabra\""), Object::natural_string("simsalabim 9223372036854776000 abracadabra"));
}


#[test]
fn lists() {
    assert_seq!(eval("[]"), Object::list(()));
    assert_seq!(eval("[1]"), Object::list((1,)));
    assert_seq!(eval("[1, 2, false]"), Object::list((1, 2, false)));
    assert_seq!(eval("[1, 2, 3, 4, 5]"), Object::list((1, 2, 3, 4, 5)));

    assert_seq!(eval("[1, false, \"dingbob\", 2.2, null]"), Object::list((
        1, false, "dingbob", 2.2, Object::Null
    )));
}


#[test]
fn maps() {
    assert_seq!(eval("{}"), Object::map(()));

    assert_seq!(eval("{a: -1, b: true, c: \"\", d: 3.14, e: null}"), Object::map((
        ("a", -1),
        ("b", true),
        ("c", ""),
        ("d", 3.14),
        ("e", Object::Null),
    )));

    assert_seq!(eval("{$\"a\": 1}"), Object::map((("a", 1),)));
    assert_seq!(eval("{$\"abcdefghijklmnopqrstuvwxyz\": 1}"), Object::map((("abcdefghijklmnopqrstuvwxyz", 1),)));
}


#[test]
fn let_bindings() {
    assert_seq!(eval("let a = 1 in a"), Object::from(1));
    assert_seq!(eval("let a = 1 let b = a in b"), Object::from(1));
    assert_seq!(eval("let a = 1 let b = a in a"), Object::from(1));

    assert_seq!(eval("let a = 1 let b = \"zomg\" in [a, b]"), Object::list((1, "zomg")));
    assert_seq!(eval("let a = 1 let b = let a = 2 in a in [a, b]"), Object::list((1, 2)));
    assert_seq!(eval("let a = 1 let b = a let a = 2 in [a, b]"), Object::list((2, 1)));

    assert!(eval("let a = 1 let b = a in y").is_err());
}


#[test]
fn list_bindings() {
    assert_seq!(eval("let [a] = [1] in a"), Object::from(1));
    assert_seq!(eval("let [a, ...] = [1] in a"), Object::from(1));
    assert_seq!(eval("let [a, ...] = [1, 2, 3] in a"), Object::from(1));
    assert_seq!(eval("let [_, a, ...] = [1, 2, 3] in a"), Object::from(2));
    assert_seq!(eval("let [_, _, a, ...] = [1, 2, 3] in a"), Object::from(3));
    assert_seq!(eval("let [_, _, a] = [1, 2, 3] in a"), Object::from(3));

    assert_seq!(eval("let [...a] = [1, 2, 3] in a"), Object::list((1, 2, 3)));
    assert_seq!(eval("let [...a, _] = [1, 2, 3] in a"), Object::list((1, 2)));
    assert_seq!(eval("let [...a, _, _] = [1, 2, 3] in a"), Object::list((1,)));
    assert_seq!(eval("let [_, ...a, _] = [1, 2, 3] in a"), Object::list((2,)));

    assert_seq!(eval("let [_, ...a, _, _] = [1, 2, 3] in a"), Object::list(()));

    assert_seq!(eval("let [a = 1] = [] in a"), Object::from(1));
    assert_seq!(eval("let [b, a = 1] = [2] in b"), Object::from(2));
    assert_seq!(eval("let [b, a = 1] = [2] in a"), Object::from(1));
    assert_seq!(eval("let [b = 3, a = 1] = [2] in a"), Object::from(1));
    assert_seq!(eval("let [b = 3, a = 1] = [2] in b"), Object::from(2));

    assert!(eval("let [x] = [1, 2, 3] in x").is_err());
    assert!(eval("let [x, y, z, a, ...] = [1, 2, 3] in x").is_err());
    assert!(eval("let [x, ..., y, z, a] = [1, 2, 3] in x").is_err());
    assert!(eval("let [x] = [] in x").is_err());
    assert!(eval("let [x, y = 1] = [] in x").is_err());
    assert!(eval("let [x = 1, y] = [] in x").is_err());

    assert_seq!(eval("let [a,b] = [1,2] in {a: a, b: b}"), Object::map((("a", 1), ("b", 2))));
    assert_seq!(eval("let [a,[b]] = [1,[2]] in {a: a, b: b}"), Object::map((("a", 1), ("b", 2))));
    assert_seq!(eval("let [a, b = 1, ...c] = [2] in [a, b, c]"), Object::list((2, 1, Object::list(()))));
}


#[test]
fn map_bindings() {
    assert_seq!(eval("let {a} = {a: 1} in a"), Object::from(1));
    assert_seq!(eval("let {a as b} = {a: 1} in b"), Object::from(1));
    assert_seq!(eval("let {a as a} = {a: 1} in a"), Object::from(1));

    assert_seq!(eval("let {a, ...x} = {a: 1} in a"), Object::from(1));
    assert_seq!(eval("let {a, ...x} = {a: 1} in x"), Object::map(()));
    assert_seq!(eval("let {...x} = {a: 1} in x"), Object::map((("a", 1),)));
    assert_seq!(eval("let {a, ...x} = {a: 1, b: 2} in x"), Object::map((("b", 2),)));
    assert_seq!(eval("let {a, ...x} = {a: 1, b: 2} in a"), Object::from(1));

    assert_seq!(eval("let {a = 1} = {} in a"), Object::from(1));
    assert_seq!(eval("let {a as b = 1} = {} in b"), Object::from(1));

    assert!(eval("let {a} = {} in a").is_err());
    assert!(eval("let {a} = {b: 1} in a").is_err());
}


#[test]
fn function_bindings() {
    assert_seq!(eval(concat!(
        "let a = |x, [y, z]| x + y + z\n",
        "in a(1, [2, 3])"
    )), Object::from(6));

    assert_seq!(eval(concat!(
        "let f = |[y = 1]| y\n",
        "in f([])"
    )), Object::from(1));

    assert_seq!(eval(concat!(
        "let q = 1\n",
        "let f = |[y = q]| y\n",
        "in f([])"
    )), Object::from(1));

    assert_seq!(eval(concat!(
        "let f = |q| |[y = q]| y\n",
        "let q = 1\n",
        "in f(2)([])"
    )), Object::from(2));

    assert_seq!(eval(concat!(
        "let f = |x; y, z| x + y + z\n",
        "in f(1, y: 2, z: 3)"
    )), Object::from(6));

    assert_seq!(eval(concat!(
        "let f = |; y=1| y\n",
        "in f()"
    )), Object::from(1));

    assert_seq!(eval(concat!(
        "let q = 1\n",
        "let f = |; y=q| y\n",
        "in f()"
    )), Object::from(1));

    assert_seq!(eval(concat!(
        "let f = |q| |; y=q| y\n",
        "let q = 1\n",
        "in f(2)()"
    )), Object::from(2));

    assert_seq!(eval(concat!(
        "let f = |x, y=15; z=200| [x,y,z]\n",
        "in [f(1), f(1,2), f(1,z:100), f(1,2,z:100)]"
    )), Object::list((
        Object::list((1, 15, 200)),
        Object::list((1, 2, 200)),
        Object::list((1, 15, 100)),
        Object::list((1, 2, 100)),
    )));

    assert_seq!(eval(concat!(
        "let dest = |...args; ...kwargs| [args, kwargs]\n",
        "in dest()"
    )), Object::list((
        Object::list(()),
        Object::map(()),
    )));

    assert_seq!(eval(concat!(
        "let dest = |...args; ...kwargs| [args, kwargs]\n",
        "in dest(1, 2)"
    )), Object::list((
        Object::list((1, 2)),
        Object::map(()),
    )));

    assert_seq!(eval(concat!(
        "let dest = |...args; ...kwargs| [args, kwargs]\n",
        "in dest(x: 1, y: 2)"
    )), Object::list((
        Object::list(()),
        Object::map((("x", 1), ("y", 2))),
    )));

    assert_seq!(eval(concat!(
        "let dest = |...args; ...kwargs| [args, kwargs]\n",
        "in dest(1, 2, x: 3, y: 4)"
    )), Object::list((
        Object::list((1, 2)),
        Object::map((("x", 3), ("y", 4))),
    )));

    assert_seq!(eval(concat!(
        "let dest = |...args; ...kwargs| [args, kwargs]\n",
        "let args = [1, 2, 3]\n",
        "let kwargs = {x: 4, y: 5, z: 6}\n",
        "in dest(0, ...args, 5, a: 8, ...kwargs, c: 10, z: 12)"
    )), Object::list((
        Object::list((0, 1, 2, 3, 5)),
        Object::map((("a", 8), ("x", 4), ("y", 5), ("z", 12), ("c", 10))),
    )));

    assert_seq!(eval("({||} 1)()"), Object::from(1));
    assert_seq!(eval("({|a, b|} a + b)(a: 1, b: 2)"), Object::from(3));
    assert_seq!(eval("({|a, b=2|} a + b)(a: 1, b: 3)"), Object::from(4));
    assert_seq!(eval("({|a, b=2|} a + b)(a: 1)"), Object::from(3));
}


#[test]
fn arithmetic() {
    assert_seq!(eval("1 + 2"), Object::from(3));
    assert_seq!(eval("3 + 2"), Object::from(5));
    assert_seq!(eval("3 + 2 - 5"), Object::from(0));
    assert_seq!(eval("3 - -5"), Object::from(8));
    assert_seq!(eval("2 * 4"), Object::from(8));
    assert_seq!(eval("2.0 * 4"), Object::from(8.0));
    assert_seq!(eval("2 * 4.0"), Object::from(8.0));
    assert_seq!(eval("2 * 4 + 1"), Object::from(9));
    assert_seq!(eval("2 * (4 + 1)"), Object::from(10));
    assert_seq!(eval("3 / 2"), Object::from(1.5));
    assert_seq!(eval("3.0 / 2"), Object::from(1.5));
    assert_seq!(eval("3 / 2.0"), Object::from(1.5));
    assert_seq!(eval("3.0 / 2.0"), Object::from(1.5));
    assert_seq!(eval("3 // 2"), Object::from(1));
    assert_seq!(eval("1 + 2.0"), Object::from(3.0));
    assert_seq!(eval("1.0 + 2"), Object::from(3.0));
    assert_seq!(eval("1.0 + 2.0"), Object::from(3.0));
    assert_seq!(eval("1.0 - 2.0"), Object::from(-1.0));
    assert_seq!(eval("1.0 - 2"), Object::from(-1.0));
    assert_seq!(eval("1 - 2.0"), Object::from(-1.0));
    assert_seq!(eval("1 - 2 + 3"), Object::from(2));
    assert_seq!(eval("2 // 2 * 2"), Object::from(2));
    assert_seq!(eval("2 ^ 2"), Object::from(4));
    assert_seq!(eval("-2 ^ 2"), Object::from(-4));
    assert_seq!(eval("2 ^ 2 ^ 2"), Object::from(16));
    assert_seq!(eval("-2 ^ 2 ^ 2"), Object::from(-16));
    assert_seq!(eval("2 ^ 3 ^ 3"), Object::from(134217728));
    assert_seq!(eval("(2 ^ 3) ^ 3"), Object::from(512));
    assert_seq!(eval("-2 ^ 3 ^ 3"), Object::from(-134217728));
    assert_seq!(eval("(-2 ^ 3) ^ 3"), Object::from(-512));
    assert_seq!(eval("-(2 ^ 3) ^ 3"), Object::from(-512));
    assert_seq!(eval("2 ^ -1"), Object::from(0.5));

    assert_seq!(eval("(9999999999999999999999999 + 1) - 9999999999999999999999999"), Object::from(1));
    assert_seq!(eval("9223372036854775800 + 9223372036854775800 - 9223372036854775800"), Object::from(9223372036854775800_i64));
    assert_seq!(eval("(-9999999999999999999999999 - 1) + 9999999999999999999999999"), Object::from(-1));
}


#[test]
fn compare() {
    assert_seq!(eval("1 < 2"), Object::from(true));
    assert_seq!(eval("1 < 2.0"), Object::from(true));
    assert_seq!(eval("1.0 < 2"), Object::from(true));
    assert_seq!(eval("1.0 < 2.0"), Object::from(true));
    assert_seq!(eval("\"a\" < \"b\""), Object::from(true));

    assert_seq!(eval("1 > 2"), Object::from(false));
    assert_seq!(eval("1 > 2.0"), Object::from(false));
    assert_seq!(eval("1.0 > 2"), Object::from(false));
    assert_seq!(eval("1.0 > 2.0"), Object::from(false));
    assert_seq!(eval("\"a\" > \"b\""), Object::from(false));

    assert_seq!(eval("2 <= 2"), Object::from(true));
    assert_seq!(eval("2 <= 2.0"), Object::from(true));
    assert_seq!(eval("2.0 <= 2"), Object::from(true));
    assert_seq!(eval("2.0 <= 2.0"), Object::from(true));
    assert_seq!(eval("\"a\" <= \"b\""), Object::from(true));

    assert_seq!(eval("1 >= 2"), Object::from(false));
    assert_seq!(eval("1 >= 2.0"), Object::from(false));
    assert_seq!(eval("1.0 >= 2"), Object::from(false));
    assert_seq!(eval("1.0 >= 2.0"), Object::from(false));
    assert_seq!(eval("\"a\" >= \"b\""), Object::from(false));

    assert_seq!(eval("1 == 2"), Object::from(false));
    assert_seq!(eval("2 == 2"), Object::from(true));
    assert_seq!(eval("2.0 == 2.0"), Object::from(true));
    assert_seq!(eval("2 == 2.0"), Object::from(true));
    assert_seq!(eval("2.0 == 2"), Object::from(true));
    assert_seq!(eval("\"a\" == \"b\""), Object::from(false));
    assert_seq!(eval("true == false"), Object::from(false));
    assert_seq!(eval("null == null"), Object::from(true));

    assert_seq!(eval("[] == []"), Object::from(true));
    assert_seq!(eval("[1] == []"), Object::from(false));
    assert_seq!(eval("[1] == [2]"), Object::from(false));
    assert_seq!(eval("[1] == [1]"), Object::from(true));
    assert_seq!(eval("[1] == [1.0]"), Object::from(true));

    assert_seq!(eval("{} == {}"), Object::from(true));
    assert_seq!(eval("{a: 1} == {}"), Object::from(false));
    assert_seq!(eval("{a: 1} == {a: 1}"), Object::from(true));
    assert_seq!(eval("{b: 1} == {a: 1}"), Object::from(false));
    assert_seq!(eval("{a: 1.0} == {a: 1}"), Object::from(true));
    assert_seq!(eval("{a: 2} == {a: 1}"), Object::from(false));
    assert_seq!(eval("{a: 1} == {a: 1, b: 1}"), Object::from(false));
    assert_seq!(eval("{a: 1} == {a: 1, a: 1}"), Object::from(true));

    assert_seq!(eval("[] == {}"), Object::from(false));

    assert_seq!(eval("1 != 2"), Object::from(true));
    assert_seq!(eval("2 != 2"), Object::from(false));
    assert_seq!(eval("2.0 != 2.0"), Object::from(false));
    assert_seq!(eval("2 != 2.0"), Object::from(false));
    assert_seq!(eval("2.0 != 2"), Object::from(false));
    assert_seq!(eval("\"a\" != \"b\""), Object::from(true));
    assert_seq!(eval("true != false"), Object::from(true));
    assert_seq!(eval("null != null"), Object::from(false));

    assert_seq!(eval("[] != []"), Object::from(false));
    assert_seq!(eval("[1] != []"), Object::from(true));
    assert_seq!(eval("[1] != [2]"), Object::from(true));
    assert_seq!(eval("[1] != [1]"), Object::from(false));
    assert_seq!(eval("[1] != [1.0]"), Object::from(false));

    assert_seq!(eval("{} != {}"), Object::from(false));
    assert_seq!(eval("{a: 1} != {}"), Object::from(true));
    assert_seq!(eval("{a: 1} != {a: 1}"), Object::from(false));
    assert_seq!(eval("{b: 1} != {a: 1}"), Object::from(true));
    assert_seq!(eval("{a: 1.0} != {a: 1}"), Object::from(false));
    assert_seq!(eval("{a: 2} != {a: 1}"), Object::from(true));
    assert_seq!(eval("{a: 1} != {a: 1, b: 1}"), Object::from(true));
    assert_seq!(eval("{a: 1} != {a: 1, a: 1}"), Object::from(false));

    assert_seq!(eval("[] != {}"), Object::from(true));
}


#[test]
fn logic() {
    assert_seq!(eval("true and 1"), Object::from(1));
    assert_seq!(eval("false and 1"), Object::from(false));
    assert_seq!(eval("true or 1"), Object::from(true));
    assert_seq!(eval("false or 1"), Object::from(1));
    assert_seq!(eval("null or 1"), Object::from(1));
    assert_seq!(eval("1 or 1"), Object::from(1));
}


#[test]
fn list_concat() {
    assert_seq!(eval("[1, 2] + [3]"), Object::list((1, 2, 3)));
    assert_seq!(eval("[1, 2] + []"), Object::list((1, 2)));
    assert_seq!(eval("[] + [3]"), Object::list((3,)));

    assert_seq!(eval("[...[1, 2], ...[3]]"), Object::list((1, 2, 3)));
    assert_seq!(eval("[...[1, 2], ...[]]"), Object::list((1, 2)));
    assert_seq!(eval("[...[1, 2]]"), Object::list((1, 2)));
    assert_seq!(eval("[...[], ...[3]]"), Object::list((3,)));
    assert_seq!(eval("[...[3]]"), Object::list((3,)));
}


#[test]
fn map_concat() {
    assert_seq!(eval("{a: 1, ...{b: 2, c: 3}, d: 4}"), Object::map((
        ("a", 1),
        ("b", 2),
        ("c", 3),
        ("d", 4),
    )));

    assert_seq!(eval("{a: 1, ...{a: 2, c: 3}, c: 4}"), Object::map((
        ("a", 2),
        ("c", 4),
    )));
}


#[test]
fn functions() {
    assert_seq!(eval(concat!(
        "let double = |x| x + x\n",
        "let applytwice = |f,x| f(f(x))\n",
        "in applytwice(double, [1])"
    )), Object::list((1, 1, 1, 1)));

    assert_seq!(eval(concat!(
        "let a = 1\n",
        "let b = || a\n",
        "let a = 2\n",
        "in b()"
    )), Object::from(1));

    assert_seq!(eval(concat!(
        "let a = 1\n",
        "let b = |q = a| q\n",
        "in b()"
    )), Object::from(1));

    assert_seq!(eval(concat!(
        "let a = 1\n",
        "let b = |q = a| q\n",
        "let a = 2\n",
        "in b()"
    )), Object::from(1));

    assert_seq!(eval(concat!(
        "let b = || let a = 1 in |q = a| q\n",
        "let c = b()\n",
        "in c()"
    )), Object::from(1));

    assert_seq!(eval(concat!(
        "let a = |q, ...x| [q, ...x]\n",
        "in a(1, 2, 3)"
    )), Object::list((1, 2, 3)));

    assert_seq!(eval(concat!(
        "let a = |q, p = q| p\n",
        "in a(1, 2)"
    )), Object::from(2));

    assert_seq!(eval(concat!(
        "let a = |q, p = q| p\n",
        "in a(1)"
    )), Object::from(1));

    assert_seq!(eval(concat!(
        "let a = |; k = 1| k\n",
        "in a()"
    )), Object::from(1));

    assert_seq!(eval(concat!(
        "let a = |; k = 1| k\n",
        "in a(k: 2)"
    )), Object::from(2));

    assert_seq!(eval(concat!(
        "let a = {|k = 1|} k\n",
        "in a()"
    )), Object::from(1));

    assert_seq!(eval(concat!(
        "let a = {|k = 1|} k\n",
        "in a(k: 2)"
    )), Object::from(2));
}


#[test]
fn subscripting() {
    assert_seq!(eval("[1, 2, 3][0]"), Object::from(1));
    assert_seq!(eval("[1, 2, 3][1]"), Object::from(2));
    assert_seq!(eval("[1, 2, 3][2]"), Object::from(3));

    assert_seq!(eval("{a: 1, b: 2}.a"), Object::from(1));
    assert_seq!(eval("{a: 1, b: 2}.b"), Object::from(2));
    assert_seq!(eval("{a: 1, b: 2}[\"a\"]"), Object::from(1));
    assert_seq!(eval("{a: 1, b: 2}[\"b\"]"), Object::from(2));
}


#[test]
fn branching_in_collections() {
    assert_seq!(eval("[if true then 1 else 2, 3]"), Object::list((1, 3)));
    assert_seq!(eval("[if false then 1 else 2, 3]"), Object::list((2, 3)));
}


#[test]
fn conditional_collection_elements() {
    assert_seq!(eval("[when true: 1, when false: 2, if true then 3 else 4, 5]"), Object::list((1, 3, 5)));
    assert_seq!(eval("{a: if true then 1 else 2, when true: b: 3, when false: c: 4}"), Object::map((("a", 1), ("b", 3))));
}


#[test]
fn iterable_collection_elements() {
    assert_seq!(eval("let a = [1, 2, 3] in [for x in a: x + 1]"), Object::list((2, 3, 4)));
    assert_seq!(eval("{for [x,y] in [[\"a\", 1], [\"b\", 2]]: $x: y}"), Object::map((("a", 1), ("b", 2))));
}


#[test]
fn complex_collection_elements() {
    assert_seq!(eval(concat!(
        "let a = [1, 2, 3, 4, 5]\n",
        "in [for x in a: when x < 3: x]"
    )), Object::list((1, 2)));

    assert_seq!(eval(concat!(
        "let a = [[1], [2, 3], [4, 5, 6]]\n",
        "in [for x in a: when len(x) > 1: ...x]"
    )), Object::list((2, 3, 4, 5, 6)));

    assert_seq!(eval(concat!(
        "let a = [[\"x\",1], [\"y\",2], [\"z\",3]]\n",
        "in {for [x,y] in a: when y != 2: $x: y}"
    )), Object::map((("x", 1), ("z", 3))));
}


#[test]
fn builtins() {
    assert_seq!(eval("len([1, 2])"), Object::from(2));
    assert_seq!(eval("len([])"), Object::from(0));

    assert_seq!(eval("len({})"), Object::from(0));
    assert_seq!(eval("len({a: 1})"), Object::from(1));

    assert_seq!(eval("len(\"\")"), Object::from(0));
    assert_seq!(eval("len(\"abc\")"), Object::from(3));
    assert_seq!(eval("len(\"å\")"), Object::from(1));

    assert_seq!(eval("range(3)"), Object::list((0, 1, 2)));
    assert_seq!(eval("range(1, 3)"), Object::list((1, 2)));

    assert_seq!(eval("int(1)"), Object::from(1));
    assert_seq!(eval("int(true)"), Object::from(1));
    assert_seq!(eval("int(false)"), Object::from(0));
    assert_seq!(eval("int(1.2)"), Object::from(1));
    assert_seq!(eval("int(-1.2)"), Object::from(-1));
    assert_seq!(eval("int(\"-3\")"), Object::from(-3));

    assert_seq!(eval("bool(1)"), Object::from(true));
    assert_seq!(eval("bool(0)"), Object::from(false));
    assert_seq!(eval("bool(1.5)"), Object::from(true));
    assert_seq!(eval("bool(0.0)"), Object::from(false));
    assert_seq!(eval("bool(true)"), Object::from(true));
    assert_seq!(eval("bool(false)"), Object::from(false));
    assert_seq!(eval("bool(null)"), Object::from(false));
    assert_seq!(eval("bool([])"), Object::from(true));
    assert_seq!(eval("bool({})"), Object::from(true));

    assert_seq!(eval("str(1)"), Object::from("1"));
    assert_seq!(eval("str(1.2)"), Object::from("1.2"));
    assert_seq!(eval("str(\"delta\")"), Object::from("delta"));
    assert_seq!(eval("str(true)"), Object::from("true"));
    assert_seq!(eval("str(false)"), Object::from("false"));
    assert_seq!(eval("str(null)"), Object::from("null"));

    assert_seq!(eval("float(1)"), Object::from(1.0));
    assert_seq!(eval("float(1.0)"), Object::from(1.0));
    assert_seq!(eval("float(true)"), Object::from(1.0));
    assert_seq!(eval("float(false)"), Object::from(0.0));
    assert_seq!(eval("float(\"1.2\")"), Object::from(1.2));
}


macro_rules! loc {
    ($loc:expr, $act:ident) => {
        (Span::from($loc), Action::$act)
    };
}


macro_rules! err {
    ($reason:expr, $($locs:expr),*) => {
        Err(Error {
            locations: Some(vec![$($locs),*]),
            reason: Some(Reason::from($reason)),
            rendered: None,
        })
    }
}


#[test]
fn errors() {
    assert_eq!(eval("a"), err!(Reason::Unbound("a".key()), loc!(0, LookupName)));
    assert_eq!(eval("let [a] = [] in a"), err!(Unpack::ListTooShort, loc!(5, Bind), loc!(4..7, Bind)));
    assert_eq!(eval("let [a] = [1, 2] in a"), err!(Unpack::ListTooLong, loc!(4..7, Bind)));
    assert_eq!(eval("let {a} = {} in a"), err!(Unpack::KeyMissing("a".key()), loc!(5, Bind), loc!(4..7, Bind)));
    assert_eq!(eval("let [a] = 1 in a"), err!(Unpack::TypeMismatch(BindingType::List, Type::Integer), loc!(4..7, Bind)));
    assert_eq!(eval("let {a} = true in a"), err!(Unpack::TypeMismatch(BindingType::Map, Type::Boolean), loc!(4..7, Bind)));
    assert_eq!(eval("[...1]"), err!(TypeMismatch::SplatList(Type::Integer), loc!(4, Splat)));
    assert_eq!(eval("[for x in 1: x]"), err!(TypeMismatch::Iterate(Type::Integer), loc!(10, Iterate)));
    assert_eq!(eval("{$null: 1}"), err!(TypeMismatch::MapKey(Type::Null), loc!(2..6, Assign)));
    assert_eq!(eval("{...[]}"), err!(TypeMismatch::SplatMap(Type::List), loc!(4..6, Splat)));
    assert_eq!(eval("{for x in 2.2: a: x}"), err!(TypeMismatch::Iterate(Type::Float), loc!(10..13, Iterate)));
    assert_eq!(eval("(|...x| 1)(...true)"), err!(TypeMismatch::SplatArg(Type::Boolean), loc!(14..18, Splat)));
    assert_eq!(eval("1 + true"), err!(TypeMismatch::BinOp(Type::Integer, Type::Boolean, BinOp::Add), loc!(2, Evaluate)));
    assert_eq!(eval("\"t\" - 9"), err!(TypeMismatch::BinOp(Type::String, Type::Integer, BinOp::Subtract), loc!(4, Evaluate)));
    assert_eq!(eval("[] * 9"), err!(TypeMismatch::BinOp(Type::List, Type::Integer, BinOp::Multiply), loc!(3, Evaluate)));
    assert_eq!(eval("9 / {}"), err!(TypeMismatch::BinOp(Type::Integer, Type::Map, BinOp::Divide), loc!(2, Evaluate)));
    assert_eq!(eval("null // {}"), err!(TypeMismatch::BinOp(Type::Null, Type::Map, BinOp::IntegerDivide), loc!(5..7, Evaluate)));
    assert_eq!(eval("null < true"), err!(TypeMismatch::BinOp(Type::Null, Type::Boolean, BinOp::Less), loc!(5, Evaluate)));
    assert_eq!(eval("1 > \"\""), err!(TypeMismatch::BinOp(Type::Integer, Type::String, BinOp::Greater), loc!(2, Evaluate)));
    assert_eq!(eval("[] <= 2.1"), err!(TypeMismatch::BinOp(Type::List, Type::Float, BinOp::LessEqual), loc!(3..5, Evaluate)));
    assert_eq!(eval("{} >= false"), err!(TypeMismatch::BinOp(Type::Map, Type::Boolean, BinOp::GreaterEqual), loc!(3..5, Evaluate)));
    assert_eq!(eval("\"${[]}\""), err!(TypeMismatch::Interpolate(Type::List), loc!(3..5, Format)));
    assert_eq!(eval("\"${{}}\""), err!(TypeMismatch::Interpolate(Type::Map), loc!(3..5, Format)));
    assert_eq!(eval("-null"), err!(TypeMismatch::UnOp(Type::Null, UnOp::ArithmeticalNegate), loc!(0, Evaluate)));
    assert_eq!(eval("null[2]"), err!(TypeMismatch::BinOp(Type::Null, Type::Integer, BinOp::Index), loc!(4..7, Evaluate)));
    assert_eq!(eval("2[null]"), err!(TypeMismatch::BinOp(Type::Integer, Type::Null, BinOp::Index), loc!(1..7, Evaluate)));
    assert_eq!(eval("(2).x"), err!(TypeMismatch::BinOp(Type::Integer, Type::String, BinOp::Index), loc!(3, Evaluate)));
    assert_eq!(eval("{a: 1}.b"), err!(Reason::Unassigned("b".key()), loc!(6, Evaluate)));
    assert_eq!(
        eval("{a: 1}[\"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\"]"),
        err!(Reason::Unassigned("bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".key()), loc!(6..66, Evaluate))
    );
    assert_eq!(eval("[]()"), err!(TypeMismatch::Call(Type::List), loc!(2..4, Evaluate)));
    assert_eq!(eval("true(1)"), err!(TypeMismatch::Call(Type::Boolean), loc!(4..7, Evaluate)));

    assert_eq!(eval("range()"), err!(TypeMismatch::ArgCount(1, 2, 0), loc!(5..7, Evaluate)));
    assert_eq!(eval("range(1, 2, 3)"), err!(TypeMismatch::ArgCount(1, 2, 3), loc!(5..14, Evaluate)));
    assert_eq!(eval("len(1)"), err!(TypeMismatch::ExpectedArg(0, vec![Type::String, Type::List, Type::Map], Type::Integer), loc!(3..6, Evaluate)));
    assert_eq!(eval("len(true)"), err!(TypeMismatch::ExpectedArg(0, vec![Type::String, Type::List, Type::Map], Type::Boolean), loc!(3..9, Evaluate)));

    assert!(eval_errstr("a").is_some_and(|x| x.contains("\na\n^\n")));
    assert!(eval_errstr("\n\na\n").is_some_and(|x| x.contains("\na\n^\n")));
    assert!(eval_errstr("  a  \n").is_some_and(|x| x.contains("\n  a  \n  ^\n")));
    assert!(eval_errstr("\n  a  \n").is_some_and(|x| x.contains("\n  a  \n  ^\n")));
    assert!(eval_errstr("\n  bingbong  \n").is_some_and(|x| x.contains("\n  bingbong  \n  ^^^^^^^^\n")));

    assert!(eval_errstr(concat!(
        "let f = |x| x + 1\n",
        "let g = |x| f(x)\n",
        "let h = |x| g(x)\n",
        "in h(null)",
    )).is_some_and(|x|
        x.contains(concat!(
            "let f = |x| x + 1\n",
            "              ^",
        )) && x.contains(concat!(
            "let g = |x| f(x)\n",
            "             ^^^",
        )) && x.contains(concat!(
            "let h = |x| g(x)\n",
            "             ^^^",
        )) && x.contains(concat!(
            "in h(null)\n",
            "    ^^^^^",
        ))
    ));
}
