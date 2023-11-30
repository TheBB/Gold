use core::cmp::Ordering;

use crate::{object::Object, ast::{FormatSpec, AlignSpec, SignSpec, IntegerFormatType, FormatType, UppercaseSpec, GroupingSpec, FloatFormatType}};


#[test]
fn to_string() {
    assert_eq!(Object::int(1).to_string(), "1");
    assert_eq!(Object::int(-1).to_string(), "-1");
    assert_eq!(Object::bigint("9223372036854775808").unwrap().to_string(), "9223372036854775808");

    assert_eq!(Object::float(1.2).to_string(), "1.2");
    assert_eq!(Object::float(1.0).to_string(), "1");

    assert_eq!(Object::float(-1.2).to_string(), "-1.2");
    assert_eq!(Object::float(-1.0).to_string(), "-1");

    assert_eq!(Object::bool(true).to_string(), "true");
    assert_eq!(Object::bool(false).to_string(), "false");
    assert_eq!(Object::null().to_string(), "null");

    assert_eq!(Object::str("alpha").to_string(), "\"alpha\"");
    assert_eq!(Object::str("\"alpha\\").to_string(), "\"\\\"alpha\\\\\"");

    assert_eq!(Object::list(()).to_string(), "[]");
    assert_eq!(Object::list(vec![
        Object::int(1),
        Object::str("alpha")
    ]).to_string(), "[1, \"alpha\"]");

    assert_eq!(Object::map(()).to_string(), "{}");
    assert_eq!(Object::map(vec![("a", Object::int(1)),]).to_string(), "{a: 1}");
}


#[test]
fn format() {
    assert_eq!(Object::str("alpha").format(Default::default()), Ok("alpha".to_string()));
    assert_eq!(Object::str("\"alpha\"").format(Default::default()), Ok("\"alpha\"".to_string()));
    assert_eq!(Object::str("\"al\\pha\"").format(Default::default()), Ok("\"al\\pha\"".to_string()));
    assert_eq!(Object::bool(true).format(Default::default()), Ok("true".to_string()));
    assert_eq!(Object::bool(false).format(Default::default()), Ok("false".to_string()));
    assert_eq!(Object::null().format(Default::default()), Ok("null".to_string()));
    assert_eq!(Object::int(0).format(Default::default()), Ok("0".to_string()));
    assert_eq!(Object::int(-2).format(Default::default()), Ok("-2".to_string()));
    assert_eq!(Object::int(5).format(Default::default()), Ok("5".to_string()));

    assert_eq!(
        Object::str("dong").format(
            FormatSpec { fill: ' ', width: Some(10), ..Default::default() }
        ),
        Ok("dong      ".to_string()),
    );

    assert_eq!(
        Object::str("dong").format(
            FormatSpec { fill: ' ', width: Some(2), ..Default::default() }
        ),
        Ok("dong".to_string()),
    );

    assert_eq!(
        Object::str("dong").format(
            FormatSpec { fill: ' ', width: Some(12), align: Some(AlignSpec::left()), ..Default::default() }
        ),
        Ok("dong        ".to_string()),
    );

    assert_eq!(
        Object::str("dong").format(
            FormatSpec { fill: ' ', width: Some(8), align: Some(AlignSpec::right()), ..Default::default() }
        ),
        Ok("    dong".to_string()),
    );

    assert_eq!(
        Object::str("dong").format(
            FormatSpec { fill: ' ', width: Some(8), align: Some(AlignSpec::center()), ..Default::default() }
        ),
        Ok("  dong  ".to_string()),
    );

    assert_eq!(
        Object::str("dong").format(
            FormatSpec { fill: ' ', width: Some(7), align: Some(AlignSpec::center()), ..Default::default() }
        ),
        Ok(" dong  ".to_string()),
    );

    assert_eq!(
        Object::str("dong").format(
            FormatSpec { fill: '~', width: Some(8), align: Some(AlignSpec::center()), ..Default::default() }
        ),
        Ok("~~dong~~".to_string()),
    );

    assert_eq!(
        Object::bool(true).format(
            FormatSpec { fill: '~', width: Some(8), align: Some(AlignSpec::center()), ..Default::default() }
        ),
        Ok("~~true~~".to_string()),
    );

    assert_eq!(
        Object::bool(false).format(
            FormatSpec { fmt_type: Some(FormatType::Integer(IntegerFormatType::Decimal)), ..Default::default() }
        ),
        Ok("0".to_string()),
    );

    assert_eq!(
        Object::bool(true).format(
            FormatSpec { fmt_type: Some(FormatType::Integer(IntegerFormatType::Decimal)), ..Default::default() }
        ),
        Ok("1".to_string()),
    );

    assert_eq!(
        Object::bool(false).format(
            FormatSpec { fill: ' ', width: Some(6), align: Some(AlignSpec::right()), ..Default::default() }
        ),
        Ok(" false".to_string()),
    );

    assert_eq!(
        Object::null().format(
            FormatSpec { fill: ' ', width: Some(6), align: Some(AlignSpec::center()), ..Default::default() }
        ),
        Ok(" null ".to_string()),
    );

    assert_eq!(
        Object::int(0).format(
            FormatSpec {
                sign: Some(SignSpec::Plus),
                ..Default::default()
            }
        ),
        Ok("+0".to_string()),
    );

    assert_eq!(
        Object::int(15).format(
            FormatSpec {
                sign: Some(SignSpec::Space),
                ..Default::default()
            }
        ),
        Ok(" 15".to_string()),
    );

    assert_eq!(
        Object::int(11).format(
            FormatSpec {
                sign: Some(SignSpec::Minus),
                ..Default::default()
            }
        ),
        Ok("11".to_string()),
    );

    assert_eq!(
        Object::int(-1).format(
            FormatSpec {
                sign: Some(SignSpec::Plus),
                ..Default::default()
            }
        ),
        Ok("-1".to_string()),
    );

    assert_eq!(
        Object::int(-13).format(
            FormatSpec {
                sign: Some(SignSpec::Space),
                ..Default::default()
            }
        ),
        Ok("-13".to_string()),
    );

    assert_eq!(
        Object::int(-10).format(
            FormatSpec {
                sign: Some(SignSpec::Minus),
                ..Default::default()
            }
        ),
        Ok("-10".to_string()),
    );

    assert_eq!(
        Object::int(15).format(
            FormatSpec {
                align: Some(AlignSpec::left()),
                width: Some(10),
                ..Default::default()
            }
        ),
        Ok("15        ".to_string()),
    );

    assert_eq!(
        Object::int(15).format(
            FormatSpec {
                align: Some(AlignSpec::center()),
                width: Some(10),
                ..Default::default()
            }
        ),
        Ok("    15    ".to_string()),
    );

    assert_eq!(
        Object::int(15).format(
            FormatSpec {
                align: Some(AlignSpec::right()),
                width: Some(10),
                ..Default::default()
            }
        ),
        Ok("        15".to_string()),
    );

    assert_eq!(
        Object::int(-15).format(
            FormatSpec {
                align: Some(AlignSpec::left()),
                width: Some(10),
                ..Default::default()
            }
        ),
        Ok("-15       ".to_string()),
    );

    assert_eq!(
        Object::int(-15).format(
            FormatSpec {
                align: Some(AlignSpec::center()),
                width: Some(10),
                ..Default::default()
            }
        ),
        Ok("   -15    ".to_string()),
    );

    assert_eq!(
        Object::int(-15).format(
            FormatSpec {
                align: Some(AlignSpec::right()),
                width: Some(10),
                ..Default::default()
            }
        ),
        Ok("       -15".to_string()),
    );

    assert_eq!(
        Object::int(-15).format(
            FormatSpec {
                align: Some(AlignSpec::AfterSign),
                width: Some(10),
                ..Default::default()
            }
        ),
        Ok("-       15".to_string()),
    );

    assert_eq!(
        Object::int(15).format(
            FormatSpec {
                align: Some(AlignSpec::AfterSign),
                width: Some(10),
                ..Default::default()
            }
        ),
        Ok("        15".to_string()),
    );

    assert_eq!(
        Object::int(23).format(
            FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Decimal)),
                ..Default::default()
            }
        ),
        Ok("23".to_string()),
    );

    assert_eq!(
        Object::int(23).format(
            FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Binary)),
                ..Default::default()
            }
        ),
        Ok("10111".to_string()),
    );

    assert_eq!(
        Object::int(23).format(
            FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Octal)),
                ..Default::default()
            }
        ),
        Ok("27".to_string()),
    );

    assert_eq!(
        Object::int(42).format(
            FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Lower))),
                ..Default::default()
            }
        ),
        Ok("2a".to_string()),
    );

    assert_eq!(
        Object::int(42).format(
            FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Upper))),
                ..Default::default()
            }
        ),
        Ok("2A".to_string()),
    );

    assert_eq!(
        Object::int(23).format(
            FormatSpec {
                alternate: true,
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Decimal)),
                ..Default::default()
            }
        ),
        Ok("23".to_string()),
    );

    assert_eq!(
        Object::int(23).format(
            FormatSpec {
                alternate: true,
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Binary)),
                ..Default::default()
            }
        ),
        Ok("0b10111".to_string()),
    );

    assert_eq!(
        Object::int(23).format(
            FormatSpec {
                alternate: true,
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Octal)),
                ..Default::default()
            }
        ),
        Ok("0o27".to_string()),
    );

    assert_eq!(
        Object::int(42).format(
            FormatSpec {
                alternate: true,
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Lower))),
                ..Default::default()
            }
        ),
        Ok("0x2a".to_string()),
    );

    assert_eq!(
        Object::int(42).format(
            FormatSpec {
                alternate: true,
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Upper))),
                ..Default::default()
            }
        ),
        Ok("0X2A".to_string()),
    );

    assert_eq!(
        Object::int(12738912).format(
            FormatSpec {
                grouping: Some(GroupingSpec::Comma),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Decimal)),
                ..Default::default()
            }
        ),
        Ok("12,738,912".to_string()),
    );

    assert_eq!(
        Object::int(12738912).format(
            FormatSpec {
                grouping: Some(GroupingSpec::Underscore),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Binary)),
                ..Default::default()
            }
        ),
        Ok("1100_0010_0110_0001_0110_0000".to_string()),
    );

    assert_eq!(
        Object::int(12738912).format(
            FormatSpec {
                grouping: Some(GroupingSpec::Underscore),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Octal)),
                ..Default::default()
            }
        ),
        Ok("6046_0540".to_string()),
    );

    assert_eq!(
        Object::int(12738912).format(
            FormatSpec {
                grouping: Some(GroupingSpec::Comma),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Lower))),
                ..Default::default()
            }
        ),
        Ok("c2,6160".to_string()),
    );

    assert_eq!(
        Object::int(12738912).format(
            FormatSpec {
                width: Some(12),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Lower))),
                ..Default::default()
            }
        ),
        Ok("      c26160".to_string()),
    );

    assert_eq!(
        Object::int(12738912).format(
            FormatSpec {
                sign: Some(SignSpec::Plus),
                width: Some(12),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Lower))),
                ..Default::default()
            }
        ),
        Ok("     +c26160".to_string()),
    );

    assert_eq!(
        Object::int(12738912).format(
            FormatSpec {
                align: Some(AlignSpec::AfterSign),
                sign: Some(SignSpec::Plus),
                width: Some(12),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Lower))),
                ..Default::default()
            }
        ),
        Ok("+     c26160".to_string()),
    );

    assert_eq!(
        Object::int(12738912).format(
            FormatSpec {
                align: Some(AlignSpec::AfterSign),
                sign: Some(SignSpec::Plus),
                alternate: true,
                width: Some(12),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Lower))),
                ..Default::default()
            }
        ),
        Ok("+0x   c26160".to_string()),
    );

    assert_eq!(
        Object::int(12738912).format(
            FormatSpec {
                align: Some(AlignSpec::AfterSign),
                sign: Some(SignSpec::Plus),
                alternate: true,
                width: Some(12),
                grouping: Some(GroupingSpec::Underscore),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(UppercaseSpec::Lower))),
                ..Default::default()
            }
        ),
        Ok("+0x  c2_6160".to_string()),
    );

    assert_eq!(
        Object::float(1.234).format(
            FormatSpec {
                precision: Some(1),
                ..Default::default()
             }
        ),
        Ok("1.2".to_string()),
    );

    assert_eq!(
        Object::float(1.234).format(
            FormatSpec {
                precision: Some(6),
                ..Default::default()
             }
        ),
        Ok("1.234000".to_string()),
    );

    assert_eq!(
        Object::float(1.234).format(
            FormatSpec {
                fmt_type: Some(FormatType::Float(FloatFormatType::Fixed)),
                ..Default::default()
             }
        ),
        Ok("1.234000".to_string()),
    );

    assert_eq!(
        Object::float(1.234).format(
            FormatSpec {
                precision: Some(9),
                fmt_type: Some(FormatType::Float(FloatFormatType::Fixed)),
                ..Default::default()
             }
        ),
        Ok("1.234000000".to_string()),
    );

    assert_eq!(
        Object::float(12.34).format(
            FormatSpec {
                precision: Some(5),
                fmt_type: Some(FormatType::Float(FloatFormatType::Sci(UppercaseSpec::Lower))),
                ..Default::default()
             }
        ),
        Ok("1.23400e1".to_string()),
    );

    assert_eq!(
        Object::float(12.34).format(
            FormatSpec {
                fmt_type: Some(FormatType::Float(FloatFormatType::Sci(UppercaseSpec::Upper))),
                ..Default::default()
             }
        ),
        Ok("1.234000E1".to_string()),
    );

    assert_eq!(
        Object::float(12.34).format(
            FormatSpec {
                fmt_type: Some(FormatType::Float(FloatFormatType::General)),
                ..Default::default()
             }
        ),
        Ok("12.34".to_string()),
    );

    assert_eq!(
        Object::float(12.34).format(
            FormatSpec {
                align: Some(AlignSpec::AfterSign),
                width: Some(8),
                ..Default::default()
             }
        ),
        Ok("   12.34".to_string()),
    );

    assert_eq!(
        Object::float(-12.34).format(
            FormatSpec {
                align: Some(AlignSpec::AfterSign),
                width: Some(8),
                ..Default::default()
             }
        ),
        Ok("-  12.34".to_string()),
    );

    assert_eq!(
        Object::float(12.34).format(
            FormatSpec {
                align: Some(AlignSpec::AfterSign),
                sign: Some(SignSpec::Plus),
                width: Some(8),
                ..Default::default()
             }
        ),
        Ok("+  12.34".to_string()),
    );

    assert_eq!(
        Object::float(12.34).format(
            FormatSpec {
                align: Some(AlignSpec::left()),
                sign: Some(SignSpec::Plus),
                width: Some(8),
                ..Default::default()
             }
        ),
        Ok("+12.34  ".to_string()),
    );

    assert_eq!(
        Object::float(12.34).format(
            FormatSpec {
                align: Some(AlignSpec::center()),
                sign: Some(SignSpec::Plus),
                width: Some(8),
                ..Default::default()
             }
        ),
        Ok(" +12.34 ".to_string()),
    );

    assert_eq!(
        Object::float(1000000.0).format(
            FormatSpec {
                grouping: Some(GroupingSpec::Underscore),
                ..Default::default()
             }
        ),
        Ok("1_000_000".to_string()),
    );

    assert_eq!(
        Object::float(1000000.0).format(
            FormatSpec {
                grouping: Some(GroupingSpec::Underscore),
                precision: Some(8),
                ..Default::default()
             }
        ),
        Ok("1_000_000.00000000".to_string()),
    );
}


#[test]
fn compare() {
    assert_eq!(Object::float(0.1).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Greater));
    assert_eq!(Object::float(0.5).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Greater));
    assert_eq!(Object::float(0.9).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Greater));
    assert_eq!(Object::float(1.0).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Greater));
    assert_eq!(Object::float(0.0).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Equal));
    assert_eq!(Object::float(-0.0).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Equal));
    assert_eq!(Object::float(-0.1).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Less));
    assert_eq!(Object::float(-0.5).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Less));
    assert_eq!(Object::float(-0.9).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Less));
    assert_eq!(Object::float(-1.0).partial_cmp(&Object::bigint("0").unwrap()), Some(Ordering::Less));

    assert_eq!(Object::float(-1.0).partial_cmp(&Object::bigint("-1").unwrap()), Some(Ordering::Equal));
    assert_eq!(Object::float(-1.1).partial_cmp(&Object::bigint("-1").unwrap()), Some(Ordering::Less));
    assert_eq!(Object::float(-0.9).partial_cmp(&Object::bigint("-1").unwrap()), Some(Ordering::Greater));

    assert_eq!(Object::float(1.0).partial_cmp(&Object::bigint("1").unwrap()), Some(Ordering::Equal));
    assert_eq!(Object::float(1.1).partial_cmp(&Object::bigint("1").unwrap()), Some(Ordering::Greater));
    assert_eq!(Object::float(0.9).partial_cmp(&Object::bigint("1").unwrap()), Some(Ordering::Less));

    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::float(0.1)), Some(Ordering::Less));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::float(0.5)), Some(Ordering::Less));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::float(0.9)), Some(Ordering::Less));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::float(1.0)), Some(Ordering::Less));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::float(0.0)), Some(Ordering::Equal));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::float(-0.0)), Some(Ordering::Equal));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::float(-0.1)), Some(Ordering::Greater));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::float(-0.5)), Some(Ordering::Greater));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::float(-0.9)), Some(Ordering::Greater));
    assert_eq!(Object::bigint("0").unwrap().partial_cmp(&Object::float(-1.0)), Some(Ordering::Greater));

    assert_eq!(Object::bigint("-1").unwrap().partial_cmp(&Object::float(-1.0)), Some(Ordering::Equal));
    assert_eq!(Object::bigint("-1").unwrap().partial_cmp(&Object::float(-1.1)), Some(Ordering::Greater));
    assert_eq!(Object::bigint("-1").unwrap().partial_cmp(&Object::float(-0.9)), Some(Ordering::Less));

    assert_eq!(Object::bigint("1").unwrap().partial_cmp(&Object::float(1.0)), Some(Ordering::Equal));
    assert_eq!(Object::bigint("1").unwrap().partial_cmp(&Object::float(1.1)), Some(Ordering::Less));
    assert_eq!(Object::bigint("1").unwrap().partial_cmp(&Object::float(0.9)), Some(Ordering::Greater));
}
