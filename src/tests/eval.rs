use std::rc::Rc;

use crate::eval;
use crate::object::{Object, ToObject};


#[test]
fn booleans_and_null() {
    assert_eq!(eval("true"), Ok(true.to_object()));
    assert_eq!(eval("false"), Ok(false.to_object()));
    assert_eq!(eval("null"), Ok(Object::Null));
}

#[test]
fn strings() {
    assert_eq!(eval("\"\""), Ok("".to_object()));
    assert_eq!(eval("\"simsalabim\""), Ok("simsalabim".to_object()));
    // assert_eq!(eval("\"simsalabim ${-1} abracadabra\""), Ok("simsalabim -1 abracadabra".to_object()));
    assert_eq!(eval("\"simsalabim ${0} abracadabra\""), Ok("simsalabim 0 abracadabra".to_object()));
    assert_eq!(eval("\"simsalabim ${1} abracadabra\""), Ok("simsalabim 1 abracadabra".to_object()));
    assert_eq!(eval("\"simsalabim ${9223372036854775807} abracadabra\""), Ok("simsalabim 9223372036854775807 abracadabra".to_object()));
    assert_eq!(eval("\"simsalabim ${9223372036854776000} abracadabra\""), Ok("simsalabim 9223372036854776000 abracadabra".to_object()));
}


#[test]
fn lists() {
    assert_eq!(eval("[]"), Ok(Object::List(Rc::new(vec![]))));

    assert_eq!(eval("[1]"), Ok(Object::List(Rc::new(vec![
        1.to_object(),
    ]))));

    assert_eq!(eval("[1, 2, false]"), Ok(Object::List(Rc::new(vec![
        1.to_object(),
        2.to_object(),
        false.to_object(),
    ]))));

    assert_eq!(eval("[1, ...[2, 3, 4], 5]"), Ok(Object::List(Rc::new(vec![
        1.to_object(),
        2.to_object(),
        3.to_object(),
        4.to_object(),
        5.to_object(),
    ]))))
}


#[test]
fn let_bindings() {
    assert_eq!(eval("let a = 1 in a"), Ok(1.to_object()));
    assert_eq!(eval("let a = 1 let b = a in b"), Ok(1.to_object()));

    assert_eq!(eval("let [a] = [1] in a"), Ok(1.to_object()));
}
