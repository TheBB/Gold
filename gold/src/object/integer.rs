//! Integer implementation.

use std::cmp::Ordering;
use std::fmt::Display;
use std::iter::Step;
use std::str::FromStr;
use std::rc::Rc;

use num_bigint::{BigInt, BigUint};
use num_traits::{checked_pow, ToPrimitive};
use serde::{Deserialize, Serialize};

use crate::error::{Error, Value};

use crate::formatting::{
    AlignSpec, GroupingSpec, IntegerFormatSpec, IntegerFormatType, SignSpec, UppercaseSpec,
};

#[cfg(feature="python")]
use pyo3::{IntoPy, PyObject, Python};

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
enum IntV {
    Small(i64),
    Big(Rc<BigInt>),
}

/// The integer variant represents all possible Gold integers.
#[derive(Clone, Serialize, Deserialize, PartialEq, Debug)]
pub(crate) struct Int(IntV);

impl PartialOrd<Int> for Int {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        let Self(this) = self;
        let Self(that) = other;
        match (this, that) {
            (IntV::Small(x), IntV::Small(y)) => x.partial_cmp(y),
            (IntV::Small(x), IntV::Big(y)) => BigInt::from(*x).partial_cmp(y),
            (IntV::Big(x), IntV::Small(y)) => x.as_ref().partial_cmp(&BigInt::from(*y)),
            (IntV::Big(x), IntV::Big(y)) => x.as_ref().partial_cmp(y),
        }
    }
}

impl PartialEq<f64> for Int {
    fn eq(&self, other: &f64) -> bool {
        return self.partial_cmp(other) == Some(Ordering::Equal);
    }
}

impl PartialOrd<f64> for Int {
    fn partial_cmp(&self, other: &f64) -> Option<Ordering> {
        let Self(this) = self;
        match this {
            IntV::Small(x) => (*x as f64).partial_cmp(other),
            IntV::Big(x) => {
                // Unfortunately the bigint library doesn't perform comparison with floats.
                // Compute the floor and ceil of the float in as bignums
                let (lo, hi) = f64_to_bigs(*other);

                // A bignum is equal to a float if the floor, ceil and bignum
                // are all equal to each other.
                if x.as_ref() < &lo || x.as_ref() == &lo && lo != hi {
                    Some(Ordering::Less)
                } else if x.as_ref() > &hi || x.as_ref() == &hi && lo != hi {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Equal)
                }
            }
        }
    }
}

impl Display for Int {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(this) = self;
        match this {
            IntV::Small(r) => f.write_fmt(format_args!("{}", r)),
            IntV::Big(r) => f.write_fmt(format_args!("{}", r)),
        }
    }
}

impl Step for Int {
    fn steps_between(start: &Self, end: &Self) -> Option<usize> {
        usize::try_from(&end.sub(start)).ok()
    }

    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        Some(start.add(&Self::from(count)))
    }

    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        Some(start.sub(&Self::from(count)))
    }
}

impl Int {
    pub fn small(value: i64) -> Self {
        Self(IntV::Small(value))
    }

    pub fn big(value: BigInt) -> Self {
        let mut r = Self(IntV::Big(Rc::new(value)));
        r.normalize();
        r
    }

    /// Sum of two integers. This implements the addition operator.
    pub fn add(&self, other: &Self) -> Self {
        self.operate(other, i64::checked_add, |x, y| x + y)
    }

    /// Difference of two integers. This implements the subtraaction operator.
    pub fn sub(&self, other: &Self) -> Self {
        self.operate(other, i64::checked_sub, |x, y| x - y)
    }

    /// Product of two integers. This implements the multiplication operator.
    pub fn mul(&self, other: &Self) -> Self {
        self.operate(other, i64::checked_mul, |x, y| x * y)
    }

    /// Mathematical ratio of two integers. This implements the division operator.
    pub fn div(&self, other: &Self) -> f64 {
        self.operate(
            other,
            |x, y| Some((x as f64) / (y as f64)),
            |x, y| big_to_f64(x) / big_to_f64(y),
        )
    }

    /// Integer division.
    pub fn idiv(&self, other: &Self) -> Self {
        self.operate(other, i64::checked_div, |x, y| x / y)
    }

    /// Universal utility method for implementing operators.
    ///
    /// If both operands are integers, the `ixi` function is applied, which is
    /// allowed to fail (in case of overflow, say). If it fails, or if either
    /// operand is not an integer, both operands are converted to bignums and
    /// the `bxb` function is applied. This one may not fail.
    ///
    /// This method does not apply normalization to the result. That is the
    /// responsibility of the caller.
    fn operate<S, T, U>(
        &self,
        other: &Int,
        ixi: impl Fn(i64, i64) -> Option<S>,
        bxb: impl Fn(&BigInt, &BigInt) -> T,
    ) -> U
    where
        U: From<S> + From<T>,
    {
        let Self(this) = self;
        let Self(that) = other;
        match (this, that) {
            (IntV::Small(xx), IntV::Small(yy)) => ixi(*xx, *yy)
                .map(U::from)
                .unwrap_or_else(|| U::from(bxb(&BigInt::from(*xx), &BigInt::from(*yy)))),
            (IntV::Small(xx), IntV::Big(yy)) => U::from(bxb(&BigInt::from(*xx), yy.as_ref())),
            (IntV::Big(xx), IntV::Small(yy)) => U::from(bxb(xx.as_ref(), &BigInt::from(*yy))),
            (IntV::Big(xx), IntV::Big(yy)) => U::from(bxb(xx.as_ref(), yy.as_ref())),
        }
    }

    /// Unary (mathematical) negation.
    pub fn neg(&self) -> Self {
        let Self(this) = self;
        match this {
            IntV::Small(x) => {
                if let Some(y) = x.checked_neg() {
                    Self::from(y)
                } else {
                    Self::from(-BigInt::from(*x))
                }
            }
            IntV::Big(x) => Self::from(-x.as_ref()),
        }
    }

    /// Attempt 'small' exponentiation: if the exponent fits into `usize` and
    /// the result fits into `i64`.
    fn small_pow(&self, other: &Self) -> Option<Self> {
        let Self(this) = self;
        let Self(that) = other;
        if let (IntV::Small(x), IntV::Small(y)) = (this, that) {
            let yy: usize = (*y).try_into().ok()?;
            checked_pow(*x, yy).map(Self::from)
        } else {
            None
        }
    }

    /// Attempt 'medium' exponentiation: if the exponent fits into `u32`.
    /// This uses the `BigInt::pow` method.
    fn medium_pow(&self, other: &Self) -> Option<Self> {
        let yy: u32 = other.try_into().ok()?;
        let Self(this) = self;
        match this {
            IntV::Big(x) => Some(Self::from(x.pow(yy))),
            IntV::Small(x) => Some(Self::from(BigInt::from(*x).pow(yy))),
        }
    }

    /// Attempt 'large' exponentiation: brute force multiplication of bignums.
    /// Almost certainly pointless if `medium_pow` fails, but included for
    /// completeness.
    fn big_pow(&self, other: &Self) -> Option<Self> {
        if other.eq(&Self::from(0)) {
            return Some(Self::from(1));
        }

        let Self(this) = self;
        let Self(that) = other;

        let mut exp = match that {
            IntV::Small(x) => BigUint::try_from(*x).ok()?,
            IntV::Big(x) => BigUint::try_from(x.as_ref().clone()).ok()?,
        };

        let mut base = match this {
            IntV::Small(x) => BigInt::from(*x),
            IntV::Big(x) => x.as_ref().clone(),
        };

        let one = BigUint::from(1u8);
        let zero = BigUint::from(0u8);

        while &exp & &one == zero {
            base = &base * &base;
            exp >>= 1;
        }

        if exp == one {
            return Some(Int::from(base));
        }

        let mut acc = base.clone();
        while exp > one {
            exp >>= 1;
            base = &base * &base;
            if &exp & &one == one {
                acc *= &base;
            }
        }

        Some(Self::from(acc))
    }

    /// Attempt exponentiation. This will try, in order, three different
    /// algorithms, from fast for small numbers to slow for large numbers.
    /// Should only return None if the exponent is negative.
    pub fn pow(&self, other: &Int) -> Option<Int> {
        let mut r = self.small_pow(other)
            .or_else(|| self.medium_pow(other))
            .or_else(|| self.big_pow(other))?;
        r.normalize();
        Some(r)
    }

    /// Normalize self by converting bignums to machine integers when possible.
    /// Used as a postprocesssing step for most arithmetic operations.
    pub fn normalize(&mut self) {
        let Self(this) = self;
        if let IntV::Big(x) = this {
            if let Some(y) = x.as_ref().to_i64() {
                *self = Self(IntV::Small(y));
            }
        }
    }

    /// Convert to a float.
    pub fn to_f64(&self) -> f64 {
        let Self(this) = self;
        match this {
            IntV::Small(x) => *x as f64,
            IntV::Big(x) => big_to_f64(x.as_ref()),
        }
    }

    /// Return true if this number is nonzero.
    pub fn nonzero(&self) -> bool {
        let Self(this) = self;
        match this {
            IntV::Small(x) => *x != 0,
            IntV::Big(x) => x.as_ref() != &BigInt::from(0),
        }
    }

    /// User (not structural) equality does not differentiatie between bignums
    /// and machine integers, even though it should be impossible to create two
    /// distinct representations of the same number, as all arithmetic uses
    /// [`IntVariant::normalize`] as a postprocessing step.
    pub fn user_eq(&self, other: &Int) -> bool {
        let Self(this) = self;
        let Self(that) = other;

        match (this, that) {
            (IntV::Small(x), IntV::Small(y)) => x.eq(y),
            (IntV::Small(x), IntV::Big(y)) => y.as_ref().eq(&BigInt::from(*x)),
            (IntV::Big(x), IntV::Small(y)) => x.as_ref().eq(&BigInt::from(*y)),
            (IntV::Big(x), IntV::Big(y)) => x.eq(y),
        }
    }

    pub fn format(&self, spec: &IntegerFormatSpec) -> Result<String, Error> {
        let Self(this) = self;

        let base = match (spec.fmt_type, this) {
            (IntegerFormatType::Character, _) => {
                let codepoint = u32::try_from(self).map_err(|_| Error::new(Value::OutOfRange))?;
                let c = char::try_from(codepoint).map_err(|_| Error::new(Value::OutOfRange))?;
                return Ok(c.to_string());
            }
            (IntegerFormatType::Binary, IntV::Small(x)) => format!("{:+b}", x),
            (IntegerFormatType::Binary, IntV::Big(x)) => format!("{:+b}", x.as_ref()),
            (IntegerFormatType::Decimal, IntV::Small(x)) => format!("{:+}", x),
            (IntegerFormatType::Decimal, IntV::Big(x)) => format!("{:+}", x.as_ref()),
            (IntegerFormatType::Octal, IntV::Small(x)) => format!("{:+o}", x),
            (IntegerFormatType::Octal, IntV::Big(x)) => format!("{:+o}", x.as_ref()),
            (IntegerFormatType::Hex(UppercaseSpec::Lower), IntV::Small(x)) => format!("{:+x}", x),
            (IntegerFormatType::Hex(UppercaseSpec::Lower), IntV::Big(x)) => {
                format!("{:+x}", x.as_ref())
            }
            (IntegerFormatType::Hex(UppercaseSpec::Upper), IntV::Small(x)) => format!("{:+X}", x),
            (IntegerFormatType::Hex(UppercaseSpec::Upper), IntV::Big(x)) => {
                format!("{:+X}", x.as_ref())
            }
        };

        let mut base_digits = &base[1..];
        let mut buffer = String::new();

        match (spec.sign, self < &Self::from(0)) {
            (_, true) => {
                buffer.push('-');
            }
            (SignSpec::Plus, false) => {
                buffer.push('+');
            }
            (SignSpec::Space, false) => {
                buffer.push(' ');
            }
            _ => {}
        }

        if spec.alternate {
            match spec.fmt_type {
                IntegerFormatType::Binary => {
                    buffer += "0b";
                }
                IntegerFormatType::Octal => {
                    buffer += "0o";
                }
                IntegerFormatType::Hex(UppercaseSpec::Lower) => {
                    buffer += "0x";
                }
                IntegerFormatType::Hex(UppercaseSpec::Upper) => {
                    buffer += "0X";
                }
                _ => {}
            }
        }

        if let Some(group_spec) = spec.grouping {
            let group_size: usize = match spec.fmt_type {
                IntegerFormatType::Decimal => 3,
                _ => 4,
            };

            let group_char = match group_spec {
                GroupingSpec::Comma => ',',
                GroupingSpec::Underscore => '_',
            };

            let num_groups = (base_digits.len() + group_size - 1) / group_size;
            let first_group_size = base_digits.len() - (num_groups - 1) * group_size;

            if let (AlignSpec::AfterSign, Some(min_width)) = (spec.align, spec.width) {
                let num_width = base_digits.len() + buffer.len() + num_groups - 1;
                if num_width < min_width {
                    let extra = min_width - num_width;
                    for _ in 0..extra {
                        buffer.push(spec.fill);
                    }
                }
            }

            buffer += &base_digits[..first_group_size];
            base_digits = &base_digits[first_group_size..];

            for _ in 1..num_groups {
                buffer.push(group_char);
                buffer += &base_digits[..group_size];
                base_digits = &base_digits[group_size..];
            }
        } else {
            if let (AlignSpec::AfterSign, Some(min_width)) = (spec.align, spec.width) {
                let num_width = base_digits.len() + buffer.len();
                if num_width < min_width {
                    let extra = min_width - num_width;
                    for _ in 0..extra {
                        buffer.push(spec.fill);
                    }
                }
            }

            buffer += base_digits;
        }

        if let Some(str_spec) = spec.string_spec() {
            Ok(str_spec.format(buffer))
        } else {
            Ok(buffer)
        }
    }
}

impl From<BigInt> for Int {
    fn from(value: BigInt) -> Self {
        Self::big(value)
    }
}

impl From<i64> for Int {
    fn from(value: i64) -> Self {
        Self::small(value)
    }
}

impl From<i32> for Int {
    fn from(value: i32) -> Self {
        Self::small(value as i64)
    }
}

impl From<usize> for Int {
    fn from(x: usize) -> Self {
        i64::try_from(x)
            .map(Int::small)
            .unwrap_or_else(|_| Int::big(BigInt::from(x)))
    }
}

impl TryFrom<&Int> for u32 {
    type Error = ();

    fn try_from(value: &Int) -> Result<Self, Self::Error> {
        let Int(this) = value;
        match this {
            IntV::Small(x) => Self::try_from(*x).map_err(|_| ()),
            IntV::Big(x) => Self::try_from(x.as_ref()).map_err(|_| ()),
        }
    }
}

impl TryFrom<&Int> for i64 {
    type Error = ();

    fn try_from(value: &Int) -> Result<Self, Self::Error> {
        let Int(this) = value;
        match this {
            IntV::Small(x) => Ok(*x),
            IntV::Big(x) => Self::try_from(x.as_ref()).map_err(|_| ()),
        }
    }
}

impl TryFrom<&Int> for usize {
    type Error = ();

    fn try_from(value: &Int) -> Result<Self, Self::Error> {
        let Int(this) = value;
        match this {
            IntV::Small(x) => Self::try_from(*x).map_err(|_| ()),
            IntV::Big(x) => Self::try_from(x.as_ref()).map_err(|_| ()),
        }
    }
}

fn big_to_f64(x: &BigInt) -> f64 {
    f64::from_str(x.to_string().as_str()).unwrap()
}

fn f64_to_bigs(x: f64) -> (BigInt, BigInt) {
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

#[cfg(feature = "python")]
impl IntoPy<PyObject> for &Int {
    fn into_py(self, py: Python<'_>) -> PyObject {
        match &self.0 {
            IntV::Small(x) => x.into_py(py),
            IntV::Big(x) => x.as_ref().clone().into_py(py),
        }
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use super::f64_to_bigs;

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
}
