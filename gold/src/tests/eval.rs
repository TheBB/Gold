use crate::{Type, Object, Key};
use crate::ast::{BinOp, UnOp};
use crate::error::{Action, BindingType, Error, Reason, Span, TypeMismatch, Types, Unpack};
use crate::eval_raw;


fn eval(input: &str) -> Result<Object, Error> {
    eval_raw(input).map_err(Error::unrender)
}

fn eval_errstr(input: &str) -> Option<String> {
    eval_raw(input).err().map(|x| x.render(Some(input)).rendered().map(str::to_owned)).flatten()
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
    assert_seq!(eval("true"), Object::bool(true));
    assert_seq!(eval("false"), Object::bool(false));
    assert_seq!(eval("null"), Object::null());
}


#[test]
fn integers() {
    assert_seq!(eval("1"), Object::int(1));
    assert_seq!(eval("-1"), Object::int(-1));
    assert_seq!(eval("+1"), Object::int(1));
}


#[test]
fn floats() {
    assert_seq!(eval("2."), Object::float(2.0));
    assert_seq!(eval("1.2"), Object::float(1.2));
    assert_seq!(eval("-3e1"), Object::float(-30.0));
    assert_seq!(eval("+4e-1"), Object::float(0.4));
    assert_seq!(eval("5e+1"), Object::float(50.0));
}


#[test]
fn strings() {
    assert_seq!(eval("\"\""), Object::str_interned(""));
    assert_seq!(eval("\"simsalabim\""), Object::str_interned("simsalabim"));
    assert_seq!(eval("\"simsalabim ${-1} abracadabra\""), Object::str_natural("simsalabim -1 abracadabra"));
    assert_seq!(eval("\"simsalabim ${0} abracadabra\""), Object::str_natural("simsalabim 0 abracadabra"));
    assert_seq!(eval("\"simsalabim ${1} abracadabra\""), Object::str_natural("simsalabim 1 abracadabra"));
    assert_seq!(eval("\"simsalabim ${9223372036854775807} abracadabra\""), Object::str_natural("simsalabim 9223372036854775807 abracadabra"));
    assert_seq!(eval("\"simsalabim ${9223372036854776000} abracadabra\""), Object::str_natural("simsalabim 9223372036854776000 abracadabra"));
}


#[test]
fn lists() {
    assert_seq!(eval("[]"), Object::list(()));

    assert_seq!(eval("[1]"), Object::list(vec![
        Object::int(1)
    ]));

    assert_seq!(eval("[1, 2, false]"), Object::list(vec![
        Object::int(1),
        Object::int(2),
        Object::bool(false),
    ]));

    assert_seq!(eval("[1, 2, 3, 4, 5]"), (1..6).map(Object::int).collect());

    assert_seq!(eval("[1, false, \"dingbob\", 2.2, null]"), Object::list(vec![
        Object::int(1),
        Object::bool(false),
        Object::str_interned("dingbob"),
        Object::float(2.2),
        Object::null(),
    ]));
}


#[test]
fn maps() {
    assert_seq!(eval("{}"), Object::map(()));

    assert_seq!(eval("{a: -1, b: true, c: \"\", d: 3.14, e: null}"), Object::map(vec![
        ("a", Object::int(-1)),
        ("b", Object::bool(true)),
        ("c", Object::str_interned("")),
        ("d", Object::float(3.14)),
        ("e", Object::null()),
    ]));

    assert_seq!(eval("{$\"a\": 1}"), Object::map(vec![
        ("a", Object::int(1)),
    ]));

    assert_seq!(eval("{$\"abcdefghijklmnopqrstuvwxyz\": 1}"), Object::map(vec![
        ("abcdefghijklmnopqrstuvwxyz", Object::int(1)),
    ]));
}


#[test]
fn let_bindings() {
    assert_seq!(eval("let a = 1 in a"), Object::int(1));
    assert_seq!(eval("let a = 1 let b = a in b"), Object::int(1));
    assert_seq!(eval("let a = 1 let b = a in a"), Object::int(1));

    assert_seq!(eval("let a = 1 let b = \"zomg\" in [a, b]"), Object::list(vec![
        Object::int(1),
        Object::str_interned("zomg"),
    ]));

    assert_seq!(eval("let a = 1 let b = let a = 2 in a in [a, b]"), (1..3).map(Object::int).collect());

    assert_seq!(eval("let a = 1 let b = a let a = 2 in [a, b]"), Object::list(vec![
        Object::int(2),
        Object::int(1),
    ]));

    assert!(eval("let a = 1 let b = a in y").is_err());
}


#[test]
fn list_bindings() {
    assert_seq!(eval("let [a] = [1] in a"), Object::int(1));
    assert_seq!(eval("let [a, ...] = [1] in a"), Object::int(1));
    assert_seq!(eval("let [a, ...] = [1, 2, 3] in a"), Object::int(1));
    assert_seq!(eval("let [_, a, ...] = [1, 2, 3] in a"), Object::int(2));
    assert_seq!(eval("let [_, _, a, ...] = [1, 2, 3] in a"), Object::int(3));
    assert_seq!(eval("let [_, _, a] = [1, 2, 3] in a"), Object::int(3));

    assert_seq!(eval("let [...a] = [1, 2, 3] in a"), (1..4).map(Object::int).collect());
    assert_seq!(eval("let [...a, _] = [1, 2, 3] in a"), (1..3).map(Object::int).collect());
    assert_seq!(eval("let [...a, _, _] = [1, 2, 3] in a"), Object::list(vec![Object::int(1)]));
    assert_seq!(eval("let [_, ...a, _] = [1, 2, 3] in a"), Object::list(vec![Object::int(2)]));

    assert_seq!(eval("let [_, ...a, _, _] = [1, 2, 3] in a"), Object::list(()));

    assert_seq!(eval("let [..., a] = [1] in a"), Object::int(1));
    assert_seq!(eval("let [..., _, a] = [1, 2] in a"), Object::int(2));
    assert_seq!(eval("let [..., a=1] = [2] in a"), Object::int(2));
    assert_seq!(eval("let [..., a=1] = [] in a"), Object::int(1));
    assert_seq!(eval("let [...a, _=1] = [2] in a"), Object::new_list());

    assert_seq!(eval("let [a = 1] = [] in a"), Object::int(1));
    assert_seq!(eval("let [b, a = 1] = [2] in b"), Object::int(2));
    assert_seq!(eval("let [b, a = 1] = [2] in a"), Object::int(1));
    assert_seq!(eval("let [b = 3, a = 1] = [2] in a"), Object::int(1));
    assert_seq!(eval("let [b = 3, a = 1] = [2] in b"), Object::int(2));

    assert!(eval("let [x] = [1, 2, 3] in x").is_err());
    assert!(eval("let [x, y, z, a, ...] = [1, 2, 3] in x").is_err());
    assert!(eval("let [x, ..., y, z, a] = [1, 2, 3] in x").is_err());
    assert!(eval("let [x] = [] in x").is_err());
    assert!(eval("let [x, y = 1] = [] in x").is_err());
    assert!(eval("let [x = 1, y] = [] in x").is_err());

    assert_seq!(eval("let [a,b] = [1,2] in {a: a, b: b}"), Object::map(vec![
        ("a", Object::int(1)),
        ("b", Object::int(2)),
    ]));

    assert_seq!(eval("let [a,[b]] = [1,[2]] in {a: a, b: b}"), Object::map(vec![
        ("a", Object::int(1)),
        ("b", Object::int(2)),
    ]));

    assert_seq!(eval("let [a, b = 1, ...c] = [2] in [a, b, c]"), Object::list(vec![
        Object::int(2),
        Object::int(1),
        Object::list(()),
    ]));
}


#[test]
fn map_bindings() {
    assert_seq!(eval("let {a} = {a: 1} in a"), Object::int(1));
    assert_seq!(eval("let {a as b} = {a: 1} in b"), Object::int(1));
    assert_seq!(eval("let {a as a} = {a: 1} in a"), Object::int(1));

    assert_seq!(eval("let {a, ...x} = {a: 1} in a"), Object::int(1));
    assert_seq!(eval("let {a, ...x} = {a: 1} in x"), Object::map(()));
    assert_seq!(eval("let {...x} = {a: 1} in x"), Object::map(vec![("a", Object::int(1))]));
    assert_seq!(eval("let {a, ...x} = {a: 1, b: 2} in x"), Object::map(vec![("b", Object::int(2))]));
    assert_seq!(eval("let {a, ...x} = {a: 1, b: 2} in a"), Object::int(1));

    assert_seq!(eval("let {a = 1} = {} in a"), Object::int(1));
    assert_seq!(eval("let {a as b = 1} = {} in b"), Object::int(1));

    assert!(eval("let {a} = {} in a").is_err());
    assert!(eval("let {a} = {b: 1} in a").is_err());
}


#[test]
fn function_bindings() {
    assert_seq!(eval(concat!(
        "let a = fn (x, [y, z]) x + y + z\n",
        "in a(1, [2, 3])"
    )), Object::int(6));

    assert_seq!(eval(concat!(
        "let f = fn ([y = 1]) y\n",
        "in f([])"
    )), Object::int(1));

    assert_seq!(eval(concat!(
        "let q = 1\n",
        "let f = fn ([y = q]) y\n",
        "in f([])"
    )), Object::int(1));

    assert_seq!(eval(concat!(
        "let f = fn (q) fn ([y = q]) y\n",
        "let q = 1\n",
        "in f(2)([])"
    )), Object::int(2));

    assert_seq!(eval(concat!(
        "let f = fn (x; y, z) x + y + z\n",
        "in f(1, y: 2, z: 3)"
    )), Object::int(6));

    assert_seq!(eval(concat!(
        "let f = fn (; y=1) y\n",
        "in f()"
    )), Object::int(1));

    assert_seq!(eval(concat!(
        "let q = 1\n",
        "let f = fn (; y=q) y\n",
        "in f()"
    )), Object::int(1));

    assert_seq!(eval(concat!(
        "let f = fn (q) fn (; y=q) y\n",
        "let q = 1\n",
        "in f(2)()"
    )), Object::int(2));

    assert_seq!(eval(concat!(
        "let f = fn (x, y=15; z=200) [x,y,z]\n",
        "in [f(1), f(1,2), f(1,z:100), f(1,2,z:100)]"
    )), Object::list(vec![
        Object::list(vec![Object::int(1), Object::int(15), Object::int(200)]),
        Object::list(vec![Object::int(1), Object::int(2), Object::int(200)]),
        Object::list(vec![Object::int(1), Object::int(15), Object::int(100)]),
        Object::list(vec![Object::int(1), Object::int(2), Object::int(100)]),
    ]));

    assert_seq!(eval(concat!(
        "let dest = fn (...args; ...kwargs) [args, kwargs]\n",
        "in dest()"
    )), Object::list(vec![
        Object::list(()),
        Object::map(()),
    ]));

    assert_seq!(eval(concat!(
        "let dest = fn (...args; ...kwargs) [args, kwargs]\n",
        "in dest(1, 2)"
    )), Object::list(vec![
        (1..3).map(Object::int).collect(),
        Object::map(()),
    ]));

    assert_seq!(eval(concat!(
        "let dest = fn (...args; ...kwargs) [args, kwargs]\n",
        "in dest(x: 1, y: 2)"
    )), Object::list(vec![
        Object::list(()),
        Object::map(vec![
            ("x", Object::int(1)),
            ("y", Object::int(2)),
        ]),
    ]));

    assert_seq!(eval(concat!(
        "let dest = fn (...args; ...kwargs) [args, kwargs]\n",
        "in dest(1, 2, x: 3, y: 4)"
    )), Object::list(vec![
        (1..3).map(Object::int).collect(),
        Object::map(vec![
            ("x", Object::int(3)),
            ("y", Object::int(4)),
        ]),
    ]));

    assert_seq!(eval(concat!(
        "let dest = fn (...args; ...kwargs) [args, kwargs]\n",
        "let args = [1, 2, 3]\n",
        "let kwargs = {x: 4, y: 5, z: 6}\n",
        "in dest(0, ...args, 5, a: 8, ...kwargs, c: 10, z: 12)"
    )), Object::list(vec![
        Object::list(vec![
            Object::int(0),
            Object::int(1),
            Object::int(2),
            Object::int(3),
            Object::int(5),
        ]),
        Object::map(vec![
            ("a", Object::int(8)),
            ("x", Object::int(4)),
            ("y", Object::int(5)),
            ("z", Object::int(12)),
            ("c", Object::int(10)),
        ]),
    ]));

    assert_seq!(eval("(fn {} 1)()"), Object::int(1));
    assert_seq!(eval("(fn {a, b} a + b)(a: 1, b: 2)"), Object::int(3));
    assert_seq!(eval("(fn {a, b=2} a + b)(a: 1, b: 3)"), Object::int(4));
    assert_seq!(eval("(fn {a, b=2} a + b)(a: 1)"), Object::int(3));
}


#[test]
fn deferred() {
    assert_seq!(eval(concat!(
        "let a = fn () b\n",
        "let b = 1\n",
        "in a()",
    )), Object::int(1));
}


#[test]
fn arithmetic() {
    assert_seq!(eval("1 + 2"), Object::int(3));
    assert_seq!(eval("3 + 2"), Object::int(5));
    assert_seq!(eval("3 + 2 - 5"), Object::int(0));
    assert_seq!(eval("3 - -5"), Object::int(8));
    assert_seq!(eval("2 * 4"), Object::int(8));
    assert_seq!(eval("2.0 * 4"), Object::float(8.0));
    assert_seq!(eval("2 * 4.0"), Object::float(8.0));
    assert_seq!(eval("2 * 4 + 1"), Object::int(9));
    assert_seq!(eval("2 * (4 + 1)"), Object::int(10));
    assert_seq!(eval("3 / 2"), Object::float(1.5));
    assert_seq!(eval("3.0 / 2"), Object::float(1.5));
    assert_seq!(eval("3 / 2.0"), Object::float(1.5));
    assert_seq!(eval("3.0 / 2.0"), Object::float(1.5));
    assert_seq!(eval("3 // 2"), Object::int(1));
    assert_seq!(eval("1 + 2.0"), Object::float(3.0));
    assert_seq!(eval("1.0 + 2"), Object::float(3.0));
    assert_seq!(eval("1.0 + 2.0"), Object::float(3.0));
    assert_seq!(eval("1.0 - 2.0"), Object::float(-1.0));
    assert_seq!(eval("1.0 - 2"), Object::float(-1.0));
    assert_seq!(eval("1 - 2.0"), Object::float(-1.0));
    assert_seq!(eval("1 - 2 + 3"), Object::int(2));
    assert_seq!(eval("2 // 2 * 2"), Object::int(2));
    assert_seq!(eval("2 ^ 2"), Object::int(4));
    assert_seq!(eval("-2 ^ 2"), Object::int(-4));
    assert_seq!(eval("2 ^ 2 ^ 2"), Object::int(16));
    assert_seq!(eval("-2 ^ 2 ^ 2"), Object::int(-16));
    assert_seq!(eval("2 ^ 3 ^ 3"), Object::int(134217728));
    assert_seq!(eval("(2 ^ 3) ^ 3"), Object::int(512));
    assert_seq!(eval("-2 ^ 3 ^ 3"), Object::int(-134217728));
    assert_seq!(eval("(-2 ^ 3) ^ 3"), Object::int(-512));
    assert_seq!(eval("-(2 ^ 3) ^ 3"), Object::int(-512));
    assert_seq!(eval("2 ^ -1"), Object::float(0.5));

    assert_seq!(eval("(9999999999999999999999999 + 1) - 9999999999999999999999999"), Object::int(1));
    assert_seq!(eval("9223372036854775800 + 9223372036854775800 - 9223372036854775800"), Object::int(9223372036854775800_i64));
    assert_seq!(eval("(-9999999999999999999999999 - 1) + 9999999999999999999999999"), Object::int(-1));
}


#[test]
fn compare() {
    assert_seq!(eval("1 < 2"), Object::bool(true));
    assert_seq!(eval("1 < 2.0"), Object::bool(true));
    assert_seq!(eval("1.0 < 2"), Object::bool(true));
    assert_seq!(eval("1.0 < 2.0"), Object::bool(true));
    assert_seq!(eval("\"a\" < \"b\""), Object::bool(true));

    assert_seq!(eval("1 > 2"), Object::bool(false));
    assert_seq!(eval("1 > 2.0"), Object::bool(false));
    assert_seq!(eval("1.0 > 2"), Object::bool(false));
    assert_seq!(eval("1.0 > 2.0"), Object::bool(false));
    assert_seq!(eval("\"a\" > \"b\""), Object::bool(false));

    assert_seq!(eval("2 <= 2"), Object::bool(true));
    assert_seq!(eval("2 <= 2.0"), Object::bool(true));
    assert_seq!(eval("2.0 <= 2"), Object::bool(true));
    assert_seq!(eval("2.0 <= 2.0"), Object::bool(true));
    assert_seq!(eval("\"a\" <= \"b\""), Object::bool(true));

    assert_seq!(eval("1 >= 2"), Object::bool(false));
    assert_seq!(eval("1 >= 2.0"), Object::bool(false));
    assert_seq!(eval("1.0 >= 2"), Object::bool(false));
    assert_seq!(eval("1.0 >= 2.0"), Object::bool(false));
    assert_seq!(eval("\"a\" >= \"b\""), Object::bool(false));

    assert_seq!(eval("1 == 2"), Object::bool(false));
    assert_seq!(eval("2 == 2"), Object::bool(true));
    assert_seq!(eval("2.0 == 2.0"), Object::bool(true));
    assert_seq!(eval("2 == 2.0"), Object::bool(true));
    assert_seq!(eval("2.0 == 2"), Object::bool(true));
    assert_seq!(eval("\"a\" == \"b\""), Object::bool(false));
    assert_seq!(eval("true == false"), Object::bool(false));
    assert_seq!(eval("null == null"), Object::bool(true));

    assert_seq!(eval("[] == []"), Object::bool(true));
    assert_seq!(eval("[1] == []"), Object::bool(false));
    assert_seq!(eval("[1] == [2]"), Object::bool(false));
    assert_seq!(eval("[1] == [1]"), Object::bool(true));
    assert_seq!(eval("[1] == [1.0]"), Object::bool(true));

    assert_seq!(eval("{} == {}"), Object::bool(true));
    assert_seq!(eval("{a: 1} == {}"), Object::bool(false));
    assert_seq!(eval("{a: 1} == {a: 1}"), Object::bool(true));
    assert_seq!(eval("{b: 1} == {a: 1}"), Object::bool(false));
    assert_seq!(eval("{a: 1.0} == {a: 1}"), Object::bool(true));
    assert_seq!(eval("{a: 2} == {a: 1}"), Object::bool(false));
    assert_seq!(eval("{a: 1} == {a: 1, b: 1}"), Object::bool(false));
    assert_seq!(eval("{a: 1} == {a: 1, a: 1}"), Object::bool(true));

    assert_seq!(eval("[] == {}"), Object::bool(false));

    assert_seq!(eval("1 != 2"), Object::bool(true));
    assert_seq!(eval("2 != 2"), Object::bool(false));
    assert_seq!(eval("2.0 != 2.0"), Object::bool(false));
    assert_seq!(eval("2 != 2.0"), Object::bool(false));
    assert_seq!(eval("2.0 != 2"), Object::bool(false));
    assert_seq!(eval("\"a\" != \"b\""), Object::bool(true));
    assert_seq!(eval("true != false"), Object::bool(true));
    assert_seq!(eval("null != null"), Object::bool(false));

    assert_seq!(eval("[] != []"), Object::bool(false));
    assert_seq!(eval("[1] != []"), Object::bool(true));
    assert_seq!(eval("[1] != [2]"), Object::bool(true));
    assert_seq!(eval("[1] != [1]"), Object::bool(false));
    assert_seq!(eval("[1] != [1.0]"), Object::bool(false));

    assert_seq!(eval("{} != {}"), Object::bool(false));
    assert_seq!(eval("{a: 1} != {}"), Object::bool(true));
    assert_seq!(eval("{a: 1} != {a: 1}"), Object::bool(false));
    assert_seq!(eval("{b: 1} != {a: 1}"), Object::bool(true));
    assert_seq!(eval("{a: 1.0} != {a: 1}"), Object::bool(false));
    assert_seq!(eval("{a: 2} != {a: 1}"), Object::bool(true));
    assert_seq!(eval("{a: 1} != {a: 1, b: 1}"), Object::bool(true));
    assert_seq!(eval("{a: 1} != {a: 1, a: 1}"), Object::bool(false));

    assert_seq!(eval("[] != {}"), Object::bool(true));
}


#[test]
fn containment() {
    assert_seq!(eval("[1] has 1"), Object::bool(true));
    assert_seq!(eval("[1] has 2"), Object::bool(false));
    assert_seq!(eval("\"bobloblaw\" has \"bob\""), Object::bool(true));
    assert_seq!(eval("\"bobloblaw\" has \"blob\""), Object::bool(true));
    assert_seq!(eval("\"bobloblaw\" has \"lobl\""), Object::bool(true));
    assert_seq!(eval("\"bobloblaw\" has \"shrimp\""), Object::bool(false));
}


#[test]
fn logic() {
    assert_seq!(eval("true and 1"), Object::int(1));
    assert_seq!(eval("false and 1"), Object::bool(false));
    assert_seq!(eval("true or 1"), Object::bool(true));
    assert_seq!(eval("false or 1"), Object::int(1));
    assert_seq!(eval("null or 1"), Object::int(1));
    assert_seq!(eval("1 or 1"), Object::int(1));
}


#[test]
fn list_concat() {
    assert_seq!(eval("[1, 2] + [3]"), (1..4).map(Object::int).collect());
    assert_seq!(eval("[1, 2] + []"), (1..3).map(Object::int).collect());
    assert_seq!(eval("[] + [3]"), Object::list(vec![Object::int(3)]));

    assert_seq!(eval("[...[1, 2], ...[3]]"), (1..4).map(Object::int).collect());
    assert_seq!(eval("[...[1, 2], ...[]]"), (1..3).map(Object::int).collect());
    assert_seq!(eval("[...[1, 2]]"), (1..3).map(Object::int).collect());
    assert_seq!(eval("[...[], ...[3]]"), Object::list(vec![Object::int(3)]));
    assert_seq!(eval("[...[3]]"), Object::list(vec![Object::int(3)]));
}


#[test]
fn map_concat() {
    assert_seq!(eval("{a: 1, ...{b: 2, c: 3}, d: 4}"), Object::map(vec![
        ("a", Object::int(1)),
        ("b", Object::int(2)),
        ("c", Object::int(3)),
        ("d", Object::int(4)),
    ]));

    assert_seq!(eval("{a: 1, ...{a: 2, c: 3}, c: 4}"), Object::map(vec![
        ("a", Object::int(2)),
        ("c", Object::int(4)),
    ]));
}


#[test]
fn functions() {
    assert_seq!(eval(concat!(
        "let double = fn (x) x + x\n",
        "let applytwice = fn (f,x) f(f(x))\n",
        "in applytwice(double, [1])"
    )), Object::list(vec![
        Object::int(1),
        Object::int(1),
        Object::int(1),
        Object::int(1),
    ]));

    assert_seq!(eval(concat!(
        "let a = 1\n",
        "let b = fn () a\n",
        "let a = 2\n",
        "in b()"
    )), Object::int(2));

    assert_seq!(eval(concat!(
        "let a = 1\n",
        "let b = fn (q = a) q\n",
        "in b()"
    )), Object::int(1));

    assert_seq!(eval(concat!(
        "let a = 1\n",
        "let b = fn (q = a) q\n",
        "let a = 2\n",
        "in b()"
    )), Object::int(2));

    assert_seq!(eval(concat!(
        "let b = fn () let a = 1 in fn (q = a) q\n",
        "let c = b()\n",
        "in c()"
    )), Object::int(1));

    assert_seq!(eval(concat!(
        "let a = fn (q, ...x) [q, ...x]\n",
        "in a(1, 2, 3)"
    )), (1..4).map(Object::int).collect());

    assert_seq!(eval(concat!(
        "let a = fn (q, p = q) p\n",
        "in a(1, 2)"
    )), Object::int(2));

    assert_seq!(eval(concat!(
        "let a = fn (q, p = q) p\n",
        "in a(1)"
    )), Object::int(1));

    assert_seq!(eval(concat!(
        "let a = fn (; k = 1) k\n",
        "in a()"
    )), Object::int(1));

    assert_seq!(eval(concat!(
        "let a = fn (; k = 1) k\n",
        "in a(k: 2)"
    )), Object::int(2));

    assert_seq!(eval(concat!(
        "let a = fn {k = 1} k\n",
        "in a()"
    )), Object::int(1));

    assert_seq!(eval(concat!(
        "let a = fn {k = 1} k\n",
        "in a(k: 2)"
    )), Object::int(2));

    assert_seq!(eval(concat!(
        "let a = 1\n",
        "in (fn () fn () a)()()"
    )), Object::int(1));

    assert_seq!(eval(concat!(
        "let a = 1\n",
        "in (fn () fn () fn () a)()()()"
    )), Object::int(1));
}


#[test]
fn subscripting() {
    assert_seq!(eval("[1, 2, 3][0]"), Object::int(1));
    assert_seq!(eval("[1, 2, 3][1]"), Object::int(2));
    assert_seq!(eval("[1, 2, 3][2]"), Object::int(3));

    assert_seq!(eval("{a: 1, b: 2}.a"), Object::int(1));
    assert_seq!(eval("{a: 1, b: 2}.b"), Object::int(2));
    assert_seq!(eval("{a: 1, b: 2}[\"a\"]"), Object::int(1));
    assert_seq!(eval("{a: 1, b: 2}[\"b\"]"), Object::int(2));
}


#[test]
fn branching() {
    assert_seq!(eval("if true then 1 else 2"), Object::int(1));
}


#[test]
fn branching_in_collections() {
    assert_seq!(eval("[if true then 1 else 2, 3]"), Object::list(vec![
        Object::int(1),
        Object::int(3),
    ]));

    assert_seq!(eval("[if false then 1 else 2, 3]"), Object::list(vec![
        Object::int(2),
        Object::int(3),
    ]));
}


#[test]
fn conditional_collection_elements() {
    assert_seq!(eval("[when true: 1, when false: 2, if true then 3 else 4, 5]"), Object::list(vec![
        Object::int(1),
        Object::int(3),
        Object::int(5),
    ]));

    assert_seq!(eval("{a: if true then 1 else 2, when true: b: 3, when false: c: 4}"), Object::map(vec![
        ("a", Object::int(1)),
        ("b", Object::int(3)),
    ]));
}


#[test]
fn iterable_collection_elements() {
    assert_seq!(eval("let a = [1, 2, 3] in [for x in a: x + 1]"), (2..5).map(Object::int).collect());

    assert_seq!(eval("{for [x,y] in [[\"a\", 1], [\"b\", 2]]: $x: y}"), Object::map(vec![
        ("a", Object::int(1)),
        ("b", Object::int(2))
    ]));
}


#[test]
fn complex_collection_elements() {
    assert_seq!(eval(concat!(
        "let a = [1, 2, 3, 4, 5]\n",
        "in [for x in a: when x < 3: x]"
    )), (1..3).map(Object::int).collect());

    assert_seq!(eval(concat!(
        "let a = [[1], [2, 3], [4, 5, 6]]\n",
        "in [for x in a: when len(x) > 1: ...x]"
    )), (2..7).map(Object::int).collect());

    assert_seq!(eval(concat!(
        "let a = [[\"x\",1], [\"y\",2], [\"z\",3]]\n",
        "in {for [x,y] in a: when y != 2: $x: y}"
    )), Object::map(vec![
        ("x", Object::int(1)),
        ("z", Object::int(3)),
    ]));
}


#[test]
fn builtins() {
    assert_seq!(eval("len([1, 2])"), Object::int(2));
    assert_seq!(eval("len([])"), Object::int(0));

    assert_seq!(eval("len({})"), Object::int(0));
    assert_seq!(eval("len({a: 1})"), Object::int(1));

    assert_seq!(eval("len(\"\")"), Object::int(0));
    assert_seq!(eval("len(\"abc\")"), Object::int(3));
    assert_seq!(eval("len(\"å\")"), Object::int(1));

    assert_seq!(eval("range(3)"), (0..3).map(Object::int).collect());
    assert_seq!(eval("range(1, 3)"), (1..3).map(Object::int).collect());

    assert_seq!(eval("int(1)"), Object::int(1));
    assert_seq!(eval("int(true)"), Object::int(1));
    assert_seq!(eval("int(false)"), Object::int(0));
    assert_seq!(eval("int(1.2)"), Object::int(1));
    assert_seq!(eval("int(-1.2)"), Object::int(-1));
    assert_seq!(eval("int(\"-3\")"), Object::int(-3));

    assert_seq!(eval("bool(1)"), Object::bool(true));
    assert_seq!(eval("bool(0)"), Object::bool(false));
    assert_seq!(eval("bool(1.5)"), Object::bool(true));
    assert_seq!(eval("bool(0.0)"), Object::bool(false));
    assert_seq!(eval("bool(true)"), Object::bool(true));
    assert_seq!(eval("bool(false)"), Object::bool(false));
    assert_seq!(eval("bool(null)"), Object::bool(false));
    assert_seq!(eval("bool([])"), Object::bool(true));
    assert_seq!(eval("bool({})"), Object::bool(true));

    assert_seq!(eval("str(1)"), Object::str("1"));
    assert_seq!(eval("str(1.2)"), Object::str("1.2"));
    assert_seq!(eval("str(\"delta\")"), Object::str("delta"));
    assert_seq!(eval("str(true)"), Object::str("true"));
    assert_seq!(eval("str(false)"), Object::str("false"));
    assert_seq!(eval("str(null)"), Object::str("null"));

    assert_seq!(eval("float(1)"), Object::float(1.0));
    assert_seq!(eval("float(1.0)"), Object::float(1.0));
    assert_seq!(eval("float(true)"), Object::float(1.0));
    assert_seq!(eval("float(false)"), Object::float(0.0));
    assert_seq!(eval("float(\"1.2\")"), Object::float(1.2));
}


macro_rules! loc {
    ($loc:expr, $act:ident) => {
        (Span::from($loc), Action::$act)
    };
}


macro_rules! err {
    ($reason:expr, $($locs:expr),*) => {
        Err(Error::new($reason).with_locations_vec(vec![$($locs),*]))
    }
}


#[test]
fn errors() {
    assert_eq!(eval("a"), err!(Reason::Unbound("a".key()), loc!(0, LookupName)));
    assert_eq!(eval("let [a] = [] in a"), err!(Unpack::ListTooShort, loc!(4..7, Bind)));
    assert_eq!(eval("let [a] = [1, 2] in a"), err!(Unpack::ListTooLong, loc!(4..7, Bind)));
    assert_eq!(eval("let {a} = {} in a"), err!(Unpack::KeyMissing("a".key()), loc!(5, Bind), loc!(4..7, Bind)));
    assert_eq!(eval("let [a] = 1 in a"), err!(Unpack::TypeMismatch(BindingType::List, Type::Integer), loc!(4..7, Bind)));
    assert_eq!(eval("let {a} = true in a"), err!(Unpack::TypeMismatch(BindingType::Map, Type::Boolean), loc!(4..7, Bind)));
    assert_eq!(eval("[...1]"), err!(TypeMismatch::SplatList(Type::Integer), loc!(4, Splat)));
    assert_eq!(eval("[for x in 1: x]"), err!(TypeMismatch::Iterate(Type::Integer), loc!(10, Iterate)));
    assert_eq!(eval("{$null: 1}"), err!(TypeMismatch::MapKey(Type::Null), loc!(2..6, Assign)));
    assert_eq!(eval("{...[]}"), err!(TypeMismatch::SplatMap(Type::List), loc!(4..6, Splat)));
    assert_eq!(eval("{for x in 2.2: a: x}"), err!(TypeMismatch::Iterate(Type::Float), loc!(10..13, Iterate)));
    assert_eq!(eval("(fn (...x) 1)(...true)"), err!(TypeMismatch::SplatArg(Type::Boolean), loc!(17..21, Splat)));
    assert_eq!(eval("1 + true"), err!(TypeMismatch::BinOp(Type::Integer, Type::Boolean, BinOp::Add), loc!(2, Evaluate)));
    assert_eq!(eval("\"t\" - 9"), err!(TypeMismatch::BinOp(Type::String, Type::Integer, BinOp::Subtract), loc!(4, Evaluate)));
    assert_eq!(eval("[] * 9"), err!(TypeMismatch::BinOp(Type::List, Type::Integer, BinOp::Multiply), loc!(3, Evaluate)));
    assert_eq!(eval("9 / {}"), err!(TypeMismatch::BinOp(Type::Integer, Type::Map, BinOp::Divide), loc!(2, Evaluate)));
    assert_eq!(eval("null // {}"), err!(TypeMismatch::BinOp(Type::Null, Type::Map, BinOp::IntegerDivide), loc!(5..7, Evaluate)));
    assert_eq!(eval("null < true"), err!(TypeMismatch::BinOp(Type::Null, Type::Boolean, BinOp::Less), loc!(5, Evaluate)));
    assert_eq!(eval("1 > \"\""), err!(TypeMismatch::BinOp(Type::Integer, Type::String, BinOp::Greater), loc!(2, Evaluate)));
    assert_eq!(eval("[] <= 2.1"), err!(TypeMismatch::BinOp(Type::List, Type::Float, BinOp::LessEqual), loc!(3..5, Evaluate)));
    assert_eq!(eval("{} >= false"), err!(TypeMismatch::BinOp(Type::Map, Type::Boolean, BinOp::GreaterEqual), loc!(3..5, Evaluate)));
    assert_eq!(eval("1 has 2"), err!(TypeMismatch::BinOp(Type::Integer, Type::Integer, BinOp::Contains), loc!(2..5, Evaluate)));
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

    assert_eq!(eval("range()"), err!(TypeMismatch::ArgCount { low: 1, high: 2, received: 0 }, loc!(5..7, Evaluate)));
    assert_eq!(eval("range(1, 2, 3)"), err!(TypeMismatch::ArgCount { low: 1, high: 2, received: 3 }, loc!(5..14, Evaluate)));

    assert_eq!(eval("len(1)"), err!(TypeMismatch::ExpectedPosArg{
        index: 0,
        allowed: Types::Three(Type::String, Type::List, Type::Map),
        received: Type::Integer,
    }, loc!(3..6, Evaluate)));

    assert_eq!(eval("len(true)"), err!(TypeMismatch::ExpectedPosArg{
        index: 0,
        allowed: Types::Three(Type::String, Type::List, Type::Map),
        received: Type::Boolean
    }, loc!(3..9, Evaluate)));

    assert!(eval_errstr("a").is_some_and(|x| x.contains("\na\n^\n")));
    assert!(eval_errstr("\n\na\n").is_some_and(|x| x.contains("\na\n^\n")));
    assert!(eval_errstr("  a  \n").is_some_and(|x| x.contains("\n  a  \n  ^\n")));
    assert!(eval_errstr("\n  a  \n").is_some_and(|x| x.contains("\n  a  \n  ^\n")));
    assert!(eval_errstr("\n  bingbong  \n").is_some_and(|x| x.contains("\n  bingbong  \n  ^^^^^^^^\n")));

    assert!(eval_errstr(concat!(
        "let f = fn (x) x + 1\n",
        "let g = fn (x) f(x)\n",
        "let h = fn (x) g(x)\n",
        "in h(null)",
    )).is_some_and(|x|
        x.contains(concat!(
            "let f = fn (x) x + 1\n",
            "                 ^",
        )) && x.contains(concat!(
            "let g = fn (x) f(x)\n",
            "                ^^^",
        )) && x.contains(concat!(
            "let h = fn (x) g(x)\n",
            "                ^^^",
        )) && x.contains(concat!(
            "in h(null)\n",
            "    ^^^^^",
        ))
    ));
}
