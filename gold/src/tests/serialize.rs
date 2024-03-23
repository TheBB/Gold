use crate::object::Object;

fn check(x: Object) {
    assert_eq!(
        x.serialize()
            .map(|y| Object::deserialize(&y))
            .flatten()
            .map(|x| x.0),
        Some(x)
    )
}

#[test]
fn nulls() {
    check(Object::null());
}

#[test]
fn integers() {
    check(Object::new_int(1));
    check(Object::new_int(9223372036854775807_i64));
    check(Object::new_int(-9223372036854775807_i64));
    check(Object::new_int_from_str("9223372036854775808").unwrap());
}

#[test]
fn strings() {
    check(Object::new_str(""));
    check(Object::new_str("dingbob"));
    check(Object::new_str("ding\"bob"));
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
    check(Object::from(vec![
        ("a", Object::new_int(1)),
        ("b", Object::bool(true)),
        ("c", Object::new_str("zomg")),
    ]));
}

#[test]
fn lists() {
    check(Object::from(vec![
        Object::new_int(1),
        Object::new_str("dingbob"),
        Object::float(-2.11),
        Object::bool(false),
    ]));
}
