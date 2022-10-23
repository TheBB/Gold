use std::rc::Rc;

use rug::Integer;

use crate::object::{Object, ToObject};


#[test]
fn to_string() {
    assert_eq!(1.to_object().to_string(), "1");
    assert_eq!((-1).to_object().to_string(), "-1");
    assert_eq!(
        Object::from(Integer::from_str_radix("9223372036854775808", 10).unwrap()).to_string(),
        "9223372036854775808",
    );

    assert_eq!(1.2.to_object().to_string(), "1.2");
    assert_eq!(1.0.to_object().to_string(), "1");

    assert_eq!((-1.2).to_object().to_string(), "-1.2");
    assert_eq!((-1.0).to_object().to_string(), "-1");

    assert_eq!(true.to_object().to_string(), "true");
    assert_eq!(false.to_object().to_string(), "false");
    assert_eq!(Object::Null.to_string(), "null");

    assert_eq!(Object::List(Rc::new(vec![])).to_string(), "[]");
    assert_eq!(Object::List(Rc::new(vec![
        1.to_object(),
        "alpha".to_object(),
    ])).to_string(), "[1, \"alpha\"]");

    assert_eq!("alpha".to_object().to_string(), "\"alpha\"");
    assert_eq!("\"alpha\\".to_object().to_string(), "\"\\\"alpha\\\\\"");
}


#[test]
fn format() {
    assert_eq!("alpha".to_object().fmt(), Ok("alpha".to_string()));
    assert_eq!("\"alpha\"".to_object().fmt(), Ok("\"alpha\"".to_string()));
    assert_eq!("\"al\\pha\"".to_object().fmt(), Ok("\"al\\pha\"".to_string()));
}
