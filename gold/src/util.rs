use std::str::FromStr;

use num_bigint::BigInt;


pub fn big_to_f64(x: &BigInt) -> f64 {
    f64::from_str(x.to_string().as_str()).unwrap()
}

pub fn f64_to_bigs(x: f64) -> (BigInt, BigInt) {
    let s = x.to_string();
    if let Some(i) = s.find('.') {
        let b = BigInt::from_str(&s[0..i]).unwrap();
        if x < 0.0 {
            let c = b.clone() - 1;
            (c, b)
        } else {
            let c = b.clone() + 1;
            (b, c)
        }
    } else {
        let b = BigInt::from_str(&s).unwrap();
        let c = b.clone();
        (b, c)
    }
}
