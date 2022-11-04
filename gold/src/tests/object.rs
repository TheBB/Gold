use core::cmp::Ordering;

use crate::object::Object;


#[test]
fn to_string() {
    assert_eq!(Object::from(1).to_string(), "1");
    assert_eq!(Object::from(-1).to_string(), "-1");
    assert_eq!(Object::bigint("9223372036854775808").unwrap().to_string(), "9223372036854775808");

    assert_eq!(Object::from(1.2).to_string(), "1.2");
    assert_eq!(Object::from(1.0).to_string(), "1");

    assert_eq!(Object::from(-1.2).to_string(), "-1.2");
    assert_eq!(Object::from(-1.0).to_string(), "-1");

    assert_eq!(Object::from(true).to_string(), "true");
    assert_eq!(Object::from(false).to_string(), "false");
    assert_eq!(Object::Null.to_string(), "null");

    assert_eq!(Object::from("alpha").to_string(), "\"alpha\"");
    assert_eq!(Object::from("\"alpha\\").to_string(), "\"\\\"alpha\\\\\"");

    assert_eq!(Object::list(()).to_string(), "[]");
    assert_eq!(Object::list((1, "alpha")).to_string(), "[1, \"alpha\"]");

    assert_eq!(Object::map(()).to_string(), "{}");
    assert_eq!(Object::map((("a", 1),)).to_string(), "{a: 1}");
}


#[test]
fn format() {
    assert_eq!(Object::from("alpha").format(), Ok("alpha".to_string()));
    assert_eq!(Object::from("\"alpha\"").format(), Ok("\"alpha\"".to_string()));
    assert_eq!(Object::from("\"al\\pha\"").format(), Ok("\"al\\pha\"".to_string()));
}


#[test]
fn compare() {
    assert_eq!(Object::from(0.1).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Greater));
    assert_eq!(Object::from(0.5).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Greater));
    assert_eq!(Object::from(0.9).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Greater));
    assert_eq!(Object::from(1.0).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Greater));
    assert_eq!(Object::from(0.0).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Equal));
    assert_eq!(Object::from(-0.0).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Equal));
    assert_eq!(Object::from(-0.1).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Less));
    assert_eq!(Object::from(-0.5).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Less));
    assert_eq!(Object::from(-0.9).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Less));
    assert_eq!(Object::from(-1.0).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Less));

    assert_eq!(Object::from(-1.0).partial_cmp(&Object::bigint("-1").unwrap()), Some(Ordering::Equal));
    assert_eq!(Object::from(-1.1).partial_cmp(&Object::bigint("-1").unwrap()), Some(Ordering::Less));
    assert_eq!(Object::from(-0.9).partial_cmp(&Object::bigint("-1").unwrap()), Some(Ordering::Greater));

    assert_eq!(Object::from(1.0).partial_cmp(&Object::bigint("1").unwrap()), Some(Ordering::Equal));
    assert_eq!(Object::from(1.1).partial_cmp(&Object::bigint("1").unwrap()), Some(Ordering::Greater));
    assert_eq!(Object::from(0.9).partial_cmp(&Object::bigint("1").unwrap()), Some(Ordering::Less));

    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::from(0.1)), Some(Ordering::Less));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::from(0.5)), Some(Ordering::Less));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::from(0.9)), Some(Ordering::Less));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::from(1.0)), Some(Ordering::Less));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::from(0.0)), Some(Ordering::Equal));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::from(-0.0)), Some(Ordering::Equal));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::from(-0.1)), Some(Ordering::Greater));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::from(-0.5)), Some(Ordering::Greater));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::from(-0.9)), Some(Ordering::Greater));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::from(-1.0)), Some(Ordering::Greater));

    assert_eq!(Object::bigint("-1").unwrap().partial_cmp(&Object::from(-1.0)), Some(Ordering::Equal));
    assert_eq!(Object::bigint("-1").unwrap().partial_cmp(&Object::from(-1.1)), Some(Ordering::Greater));
    assert_eq!(Object::bigint("-1").unwrap().partial_cmp(&Object::from(-0.9)), Some(Ordering::Less));

    assert_eq!(Object::bigint("1").unwrap().partial_cmp(&Object::from(1.0)), Some(Ordering::Equal));
    assert_eq!(Object::bigint("1").unwrap().partial_cmp(&Object::from(1.1)), Some(Ordering::Less));
    assert_eq!(Object::bigint("1").unwrap().partial_cmp(&Object::from(0.9)), Some(Ordering::Greater));
}
