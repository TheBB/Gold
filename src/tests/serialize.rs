use crate::object::Object;


fn check(x: Object) {
    assert_eq!(x.serialize().map(|y| Object::deserialize(&y)).flatten(), Some(x))
}


#[test]
fn nulls() {
    check(Object::Null);
}


#[test]
fn integers() {
    check(Object::from(1));
    check(Object::from(9223372036854775807_i64));
    check(Object::from(-9223372036854775807_i64));
    check(Object::bigint("9223372036854775808").unwrap());
}


#[test]
fn strings() {
    check(Object::from(""));
    check(Object::from("dingbob"));
    check(Object::from("ding\"bob"));
}


#[test]
fn bools() {
    check(Object::from(true));
    check(Object::from(false));
}


#[test]
fn floats() {
    check(Object::from(1.2234));
}


#[test]
fn maps() {
    check(Object::map((
        ("a", Object::from(1)),
        ("b", Object::from(true)),
        ("c", Object::from("zomg")),
    )));
}


#[test]
fn lists() {
    check(Object::list((1, "dingbob", -2.11, false)));
}
