use num_bigint::BigInt;

use crate::util::f64_to_bigs;


#[test]
fn to_bigs() {
    let (lo, hi) = f64_to_bigs(0.0);
    assert_eq!(lo, BigInt::from(0));
    assert_eq!(hi, BigInt::from(0));

    let (lo, hi) = f64_to_bigs(0.5);
    assert_eq!(lo, BigInt::from(0));
    assert_eq!(hi, BigInt::from(1));

    let (lo, hi) = f64_to_bigs(1.0);
    assert_eq!(lo, BigInt::from(1));
    assert_eq!(hi, BigInt::from(1));

    let (lo, hi) = f64_to_bigs(-0.5);
    assert_eq!(lo, BigInt::from(-1));
    assert_eq!(hi, BigInt::from(0));

    let (lo, hi) = f64_to_bigs(-1.0);
    assert_eq!(lo, BigInt::from(-1));
    assert_eq!(hi, BigInt::from(-1));
}
