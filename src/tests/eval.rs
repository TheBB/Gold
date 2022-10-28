use std::rc::Rc;

use crate::eval;
use crate::object::{Object};


#[test]
fn booleans_and_null() {
    assert_eq!(eval("true"), Ok(Object::from(true)));
    assert_eq!(eval("false"), Ok(Object::from(false)));
    assert_eq!(eval("null"), Ok(Object::Null));
}

#[test]
fn strings() {
    assert_eq!(eval("\"\""), Ok(Object::from("")));
    assert_eq!(eval("\"simsalabim\""), Ok(Object::from("simsalabim")));
    // assert_eq!(eval("\"simsalabim ${-1} abracadabra\""), Ok("simsalabim -1 abracadabra"));
    assert_eq!(eval("\"simsalabim ${0} abracadabra\""), Ok(Object::from("simsalabim 0 abracadabra")));
    assert_eq!(eval("\"simsalabim ${1} abracadabra\""), Ok(Object::from("simsalabim 1 abracadabra")));
    assert_eq!(eval("\"simsalabim ${9223372036854775807} abracadabra\""), Ok(Object::from("simsalabim 9223372036854775807 abracadabra")));
    assert_eq!(eval("\"simsalabim ${9223372036854776000} abracadabra\""), Ok(Object::from("simsalabim 9223372036854776000 abracadabra")));
}


#[test]
fn lists() {
    assert_eq!(eval("[]"), Ok(Object::List(Rc::new(vec![]))));

    assert_eq!(eval("[1]"), Ok(Object::List(Rc::new(vec![
        Object::from(1),
    ]))));

    assert_eq!(eval("[1, 2, false]"), Ok(Object::List(Rc::new(vec![
        Object::from(1),
        Object::from(2),
        Object::from(false),
    ]))));

    assert_eq!(eval("[1, ...[2, 3, 4], 5]"), Ok(Object::List(Rc::new(vec![
        Object::from(1),
        Object::from(2),
        Object::from(3),
        Object::from(4),
        Object::from(5),
    ]))))
}


#[test]
fn let_bindings() {
    assert_eq!(eval("let a = 1 in a"), Ok(Object::from(1)));
    assert_eq!(eval("let a = 1 let b = a in b"), Ok(Object::from(1)));

    assert_eq!(eval("let [a] = [1] in a"), Ok(Object::from(1)));
}
