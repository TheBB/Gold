use crate::object::Object;


fn check(x: Object) {
    assert_eq!(x.serialize().map(|y| Object::deserialize(&y)).flatten().map(|x| x.0), Some(x))
}


#[test]
fn nulls() {
    check(Object::null());
}


#[test]
fn integers() {
    check(Object::int(1));
    check(Object::int(9223372036854775807_i64));
    check(Object::int(-9223372036854775807_i64));
    check(Object::bigint("9223372036854775808").unwrap());
}


#[test]
fn strings() {
    check(Object::str(""));
    check(Object::str("dingbob"));
    check(Object::str("ding\"bob"));
}


#[test]
fn bools() {
    check(Object::bool(true));
    check(Object::bool(false));
}


#[test]
fn floats() {
    check(Object::float(1.2234));
}


#[test]
fn maps() {
    check(Object::map(vec![
        ("a", Object::int(1)),
        ("b", Object::bool(true)),
        ("c", Object::str("zomg")),
    ]));
}


#[test]
fn lists() {
    check(Object::list(vec![
        Object::int(1),
        Object::str("dingbob"),
        Object::float(-2.11),
        Object::bool(false),
    ]));
}
