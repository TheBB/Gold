//! A Gold object is represented by the [`Object`] type. Internally an Object
//! just wraps the [`ObjectVariant`] enumeration, which is hidden for
//! encapsulation purposes.
//!
//! The [`ObjectVariant`] type, in turn, has only unit wrappers for each of its
//! variants. Some of those variants are implemented in this module (e.g.
//! [`StrVariant`] for interned and non-interned string and [`IntVariant`] for
//! machine integers and bignums).
//!
//! User code should consider the internal structure of [`ObjectVariant`] and
//! all its variants to be unstable. Public methods on [`Object`] and
//! [`ObjectVariant`] (`Object` implements `Deref<ObjectVariant>`) are stable.


use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt::{Debug, Display};
use std::io::{Read, Write};
use std::iter::Step;
use std::str::FromStr;
use std::rc::Rc;
use std::time::SystemTime;

use json::JsonValue;
use gc::{Finalize, Gc, GcCellRef, Trace};
use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, checked_pow};
use rmp_serde::{decode, encode};
use serde::de::Visitor;
use serde::{Serialize, Serializer, Deserialize, Deserializer};
use symbol_table::GlobalSymbol;

use crate::builtins::BUILTINS;
use crate::compile::Function;
use crate::traits::{Peek, ToMap, ToVec};

use crate::ast::{ListBinding, MapBinding, Expr, BinOp, UnOp, FormatSpec, StringAlignSpec, AlignSpec, IntegerFormatType, GroupingSpec, SignSpec, UppercaseSpec, FloatFormatType};
use crate::error::{Error, Tagged, TypeMismatch, Value, Reason};
use crate::eval::Namespace;
use crate::util;
use crate::wrappers::{WBigInt, OrderedMap, GcCell};


/// This type is used for all interned strings, map keys, variable names, etc.
pub(crate) type Key = GlobalSymbol;

/// The basic type for a list of objects.
pub(crate) type List = Vec<Object>;

/// The basic type for a mapping of objects indexed by strings (in actuality, [`Key`]).
pub(crate) type Map = OrderedMap<Key, Object>;

/// The current serialization format version.
const SERIALIZE_VERSION: i32 = 1;


/// Enumerates all the possible Gold object types.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Type {
    /// IntVariant
    Integer,

    /// f64
    Float,

    /// StrVariant
    String,

    /// bool
    Boolean,

    /// Vec<Object>
    List,

    /// IndexMap<Key, Object>
    Map,

    /// FuncVariant
    Function,

    /// The empty variant
    Null,
}

// It's desirable that these names correspond to the built-in conversion
// functions. When Gold gets proper support for types, this source of ambiguity
// will be rectified.
impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer => f.write_str("int"),
            Self::Float => f.write_str("float"),
            Self::String => f.write_str("str"),
            Self::Boolean => f.write_str("bool"),
            Self::List => f.write_str("list"),
            Self::Map => f.write_str("map"),
            Self::Function => f.write_str("function"),
            Self::Null => f.write_str("null"),
        }
    }
}



// Formatting
// ------------------------------------------------------------------------------------------------

pub(crate) struct StringFormatSpec {
    pub fill: char,
    pub align: StringAlignSpec,
    pub width: Option<usize>,
}

fn fmt_str(s: &str, spec: StringFormatSpec) -> String {
    match spec.width {
        None => s.to_owned(),
        Some(w) => {
            let nchars = s.chars().count();
            if nchars > w {
                s.to_owned()
            } else {
                let missing = w - nchars;
                let (lfill, rfill) = match spec.align {
                    StringAlignSpec::Left => (0, missing),
                    StringAlignSpec::Right => (missing, 0),
                    StringAlignSpec::Center => (missing / 2, missing - missing / 2),
                };
                let mut r = String::with_capacity(w);
                for _ in 0..lfill {
                    r.push(spec.fill);
                }
                r += s;
                for _ in 0..rfill {
                    r.push(spec.fill);
                }
                r
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub(crate) struct FloatFormatSpec {
    pub fill: char,
    pub align: AlignSpec,
    pub sign: SignSpec,
    pub width: Option<usize>,
    pub grouping: Option<GroupingSpec>,
    pub precision: usize,
    pub fmt_type: FloatFormatType,
}

impl FloatFormatSpec {
    fn string_spec(&self) -> Option<StringFormatSpec> {
        match (self.align, self.width) {
            (AlignSpec::AfterSign, _) => { return None; },
            (_, None) => { return None; }
            (AlignSpec::String(align), Some(width)) => Some(
                StringFormatSpec { fill: self.fill, align, width: Some(width) }
            ),
        }
    }
}

fn fmt_float(f: f64, spec: FloatFormatSpec) -> String {
    let base = match spec.fmt_type {
        FloatFormatType::Fixed => format!("{number:+.precision$}", number = f, precision = spec.precision),
        FloatFormatType::General => format!("{:+}", f),
        FloatFormatType::Sci(UppercaseSpec::Lower) =>
            format!("{number:+.precision$e}", number = f, precision = spec.precision),
        FloatFormatType::Sci(UppercaseSpec::Upper) =>
            format!("{number:+.precision$E}", number = f, precision = spec.precision),
        FloatFormatType::Percentage =>
            format!("{number:+.precision$}%", number = 100.0*f, precision = spec.precision),
    };

    let mut base_digits = &base[1..];
    let mut buffer = String::new();

    match (spec.sign, f < 0.0) {
        (_, true) => { buffer.push('-'); },
        (SignSpec::Plus, false) => { buffer.push('+'); }
        (SignSpec::Space, false) => { buffer.push(' '); }
        _ => {},
    }

    if let Some(group_spec) = spec.grouping {
        let group_size: usize = 3;
        let group_char = match group_spec {
            GroupingSpec::Comma => ',',
            GroupingSpec::Underscore => '_',
        };

        let mut num_digits: usize = base_digits.len();
        for (i, c) in base_digits.char_indices() {
            match c {
                '0'..='9' => {},
                _ => { num_digits = i; break; }
            }
        }

        let num_groups = (num_digits + group_size - 1) / group_size;
        let first_group_size = num_digits - (num_groups - 1) * group_size;

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

        buffer += base_digits;
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
        fmt_str(buffer.as_str(), str_spec)
    } else {
        buffer
    }
}



// String variant
// ------------------------------------------------------------------------------------------------


/// Convert a string to a displayable representation by adding escape sequences.
fn escape(s: &str) -> String {
    let mut r = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => { r.push_str("\\\""); }
            '\\' => { r.push_str("\\\\"); }
            '$' => { r.push_str("\\$"); }
            _ => { r.push(c); }
        }
    }
    r
}


/// The string variant represents all possible Gold strings.
#[derive(Clone, Serialize, Deserialize, PartialEq, Debug, Trace, Finalize)]
pub enum StrVariant {
    /// Interned string. All strings that fall in the following categories are interned:
    /// - identifiers
    /// - map keys
    /// - strings no more than 20 characters long
    ///
    /// Note that Gold does not garbage-collect interned strings.
    Interned(#[unsafe_ignore_trace] Key),

    /// Natural (non-interned) string. If a string is not interned, or if it
    /// requires runtime evaluation (e.g. it is interpolated, or is the result
    /// of concatenation), then it is not interned.
    Natural(Gc<String>),
}

impl PartialOrd<StrVariant> for StrVariant {
    fn partial_cmp(&self, other: &StrVariant) -> Option<Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl From<&StrVariant> for Key {
    fn from(value: &StrVariant) -> Self {
        match value {
            StrVariant::Interned(x) => *x,
            StrVariant::Natural(x) => Key::new(x.as_ref()),
        }
    }
}

impl Display for StrVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("\"{}\"", escape(self.as_str())))
    }
}

impl StrVariant {
    /// Construct a new interned string.
    pub fn interned<T: AsRef<str>>(x: T) -> Self {
        Self::Interned(Key::new(x))
    }

    /// Construct a new natural (non-interned string).
    pub fn natural<T: AsRef<str>>(x: T) -> Self {
        Self::Natural(Gc::new(x.as_ref().to_string()))
    }

    /// Access the internal string slice.
    pub fn as_str(&self) -> &str {
        match self {
            Self::Interned(x) => x.as_str(),
            Self::Natural(x) => x.as_str(),
        }
    }

    /// User (non-structural) equality does not differentiate between interned
    /// or non-interned strings.
    fn user_eq(&self, other: &StrVariant) -> bool {
        match (self, other) {
            (Self::Interned(x), Self::Interned(y)) => x == y,
            _ => self.as_str() == other.as_str(),
        }
    }

    /// Concatenate two string variants (the + operator for strings).
    fn add(&self, other: &StrVariant) -> StrVariant {
        Self::natural(format!("{}{}", self.as_str(), other.as_str()))
    }
}



// Integer variant
// ------------------------------------------------------------------------------------------------

pub(crate) struct IntegerFormatSpec {
    pub fill: char,
    pub align: AlignSpec,
    pub sign: SignSpec,
    pub alternate: bool,
    pub width: Option<usize>,
    pub grouping: Option<GroupingSpec>,
    pub fmt_type: IntegerFormatType,
}

impl IntegerFormatSpec {
    fn string_spec(&self) -> Option<StringFormatSpec> {
        match (self.align, self.width) {
            (AlignSpec::AfterSign, _) => { return None; },
            (_, None) => { return None; }
            (AlignSpec::String(align), Some(width)) => Some(
                StringFormatSpec { fill: self.fill, align, width: Some(width) }
            ),
        }
    }
}

/// The integer variant represents all possible Gold integers.
#[derive(Clone, Serialize, Deserialize, PartialEq, Debug, Trace, Finalize)]
pub(crate) enum IntVariant {
    /// Machine integers.
    Small(i64),

    /// Bignums.
    Big(Gc<WBigInt>),
}

impl PartialOrd<IntVariant> for IntVariant {
    fn partial_cmp(&self, other: &IntVariant) -> Option<Ordering> {
        match (self, other) {
            (Self::Small(x), Self::Small(y)) => x.partial_cmp(y),
            (Self::Small(x), Self::Big(y)) => BigInt::from(*x).partial_cmp(y),
            (Self::Big(x), Self::Small(y)) => x.peek().partial_cmp(&BigInt::from(*y)),
            (Self::Big(x), Self::Big(y)) => x.peek().partial_cmp(y.peek()),
        }
    }
}

impl PartialEq<f64> for IntVariant {
    fn eq(&self, other: &f64) -> bool {
        return self.partial_cmp(other) == Some(Ordering::Equal);
    }
}

impl PartialOrd<f64> for IntVariant {
    fn partial_cmp(&self, other: &f64) -> Option<Ordering> {
        match self {
            Self::Small(x) => (*x as f64).partial_cmp(other),
            Self::Big(x) => {
                // Unfortunately the bigint library doesn't perform comparison with floats.
                // Compute the floor and ceil of the float in as bignums
                let (lo, hi) = util::f64_to_bigs(*other);

                // A bignum is equal to a float if the floor, ceil and bignum
                // are all equal to each other.
                if x.peek() < &lo || x.peek() == &lo && lo != hi {
                    Some(Ordering::Less)
                } else if x.peek() > &hi || x.peek() == &hi && lo != hi {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Equal)
                }
            },
        }
    }
}

impl From<BigInt> for IntVariant {
    fn from(value: BigInt) -> Self {
        Self::Big(Gc::new(WBigInt(value)))
    }
}

impl From<i64> for IntVariant {
    fn from(x: i64) -> Self {
        Self::Small(x)
    }
}

impl From<i32> for IntVariant {
    fn from(x: i32) -> Self {
        Self::Small(x as i64)
    }
}

impl From<usize> for IntVariant {
    fn from(x: usize) -> Self {
        i64::try_from(x).map(IntVariant::from).unwrap_or_else(
            |_| IntVariant::from(BigInt::from(x))
        )
    }
}

impl TryFrom<&IntVariant> for u32 {
    type Error = ();

    fn try_from(value: &IntVariant) -> Result<Self, Self::Error> {
        match value {
            IntVariant::Small(x) => Self::try_from(*x).map_err(|_| ()),
            IntVariant::Big(x) => Self::try_from(x.peek()).map_err(|_| ()),
        }
    }
}

impl TryFrom<&IntVariant> for i64 {
    type Error = ();

    fn try_from(value: &IntVariant) -> Result<Self, Self::Error> {
        match value {
            IntVariant::Small(x) => Ok(*x),
            IntVariant::Big(x) => Self::try_from(x.peek()).map_err(|_| ()),
        }
    }
}

impl TryFrom<&IntVariant> for usize {
    type Error = ();

    fn try_from(value: &IntVariant) -> Result<Self, Self::Error> {
        match value {
            IntVariant::Small(x) => Self::try_from(*x).map_err(|_| ()),
            IntVariant::Big(x) => Self::try_from(x.peek()).map_err(|_| ()),
        }
    }
}

impl Display for IntVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Small(r) => f.write_fmt(format_args!("{}", r)),
            Self::Big(r) => f.write_fmt(format_args!("{}", r.peek())),
        }
    }
}

impl Step for IntVariant {
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

impl IntVariant {
    /// Sum of two integers. This implements the addition operator.
    fn add(&self, other: &IntVariant) -> IntVariant {
        IntVariant::normalize(&self.operate(other, i64::checked_add, |x,y| x + y))
    }

    /// Difference of two integers. This implements the subtraaction operator.
    fn sub(&self, other: &IntVariant) -> IntVariant {
        IntVariant::normalize(&self.operate(other, i64::checked_sub, |x,y| x - y))
    }

    /// Product of two integers. This implements the multiplication operator.
    fn mul(&self, other: &IntVariant) -> IntVariant {
        IntVariant::normalize(&self.operate(other, i64::checked_mul, |x,y| x * y))
    }

    /// Mathematical ratio of two integers. This implements the division operator.
    fn div(&self, other: &IntVariant) -> f64 {
        self.operate(
            other,
            |x,y| Some((x as f64) / (y as f64)),
            |x,y| util::big_to_f64(x) / util::big_to_f64(y),
        )
    }

    /// Integer division.
    fn idiv(&self, other: &IntVariant) -> IntVariant {
        IntVariant::normalize(&self.operate(other, i64::checked_div, |x,y| x / y))
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
    fn operate<S,T,U>(
        &self,
        other: &IntVariant,
        ixi: impl Fn(i64, i64) -> Option<S>,
        bxb: impl Fn(&BigInt, &BigInt) -> T,
    ) -> U where
        U: From<S> + From<T>,
    {
        match (self, other) {
            (Self::Small(xx), Self::Small(yy)) => ixi(*xx, *yy).map(U::from).unwrap_or_else(
                || U::from(bxb(&BigInt::from(*xx), &BigInt::from(*yy)))
            ),
            (Self::Small(xx), Self::Big(yy)) => U::from(bxb(&BigInt::from(*xx), yy.peek())),
            (Self::Big(xx), Self::Small(yy)) => U::from(bxb(xx.peek(), &BigInt::from(*yy))),
            (Self::Big(xx), Self::Big(yy)) => U::from(bxb(xx.peek(), yy.peek())),
        }
    }

    /// Unary (mathematical) negation.
    fn neg(&self) -> IntVariant {
        match self {
            Self::Small(x) => {
                if let Some(y) = x.checked_neg() {
                    Self::Small(y)
                } else {
                    Self::from(-BigInt::from(*x)).normalize()
                }
            },
            Self::Big(x) => Self::from(-x.peek()).normalize(),
        }
    }

    /// Attempt 'small' exponentiation: if the exponent fits into `usize` and
    /// the result fits into `i64`.
    fn small_pow(&self, other: &IntVariant) -> Option<IntVariant> {
        if let (Self::Small(x), Self::Small(y)) = (self, other) {
            let yy: usize = (*y).try_into().ok()?;
            checked_pow(*x, yy).map(Self::from)
        } else {
            None
        }
    }

    /// Attempt 'medium' exponentiation: if the exponent fits into `u32`.
    /// This uses the `BigInt::pow` method.
    fn medium_pow(&self, other: &IntVariant) -> Option<IntVariant> {
        let yy: u32 = other.try_into().ok()?;

        match self {
            Self::Big(x) => Some(Self::from(x.pow(yy))),
            Self::Small(x) => Some(Self::from(BigInt::from(*x).pow(yy))),
        }
    }

    /// Attempt 'large' exponentiation: brute force multiplication of bignums.
    /// Almost certainly pointless if `medium_pow` fails, but included for
    /// completeness.
    fn big_pow(&self, other: &IntVariant) -> Option<IntVariant> {
        if other.eq(&IntVariant::from(0)) {
            return Some(IntVariant::from(1));
        }

        let mut exp = match other {
            Self::Small(x) => BigUint::try_from(*x).ok()?,
            Self::Big(x) => BigUint::try_from(x.peek().clone()).ok()?,
        };

        let mut base = match self {
            Self::Small(x) => BigInt::from(*x),
            Self::Big(x) => x.peek().clone(),
        };

        let one = BigUint::from(1u8);
        let zero = BigUint::from(0u8);

        while &exp & &one == zero {
            base = &base * &base;
            exp >>= 1;
        }

        if exp == one {
            return Some(IntVariant::from(base))
        }

        let mut acc = base.clone();
        while exp > one {
            exp >>= 1;
            base = &base * &base;
            if &exp & &one == one {
                acc *= &base;
            }
        }

        Some(IntVariant::from(acc))
    }

    /// Attempt exponentiation. This will try, in order, three different
    /// algorithms, from fast for small numbers to slow for large numbers.
    /// Should only return None if the exponent is negative.
    fn pow(&self, other: &IntVariant) -> Option<IntVariant> {
        self.small_pow(other)
            .or_else(|| self.medium_pow(other))
            .or_else(|| self.big_pow(other))
            .map(|x| x.normalize())
    }

    /// Normalize self by converting bignums to machine integers when possible.
    /// Used as a postprocesssing step for most arithmetic operations.
    fn normalize(&self) -> IntVariant {
        if let Self::Big(x) = &self {
            x.peek().to_i64().map(IntVariant::Small).unwrap_or_else(|| self.clone())
        } else {
            self.clone()
        }
    }

    /// Convert to a float.
    pub fn to_f64(&self) -> f64 {
        match self {
            Self::Small(x) => *x as f64,
            Self::Big(x) => util::big_to_f64(x.as_ref()),
        }
    }

    /// Return true if this number is nonzero.
    fn nonzero(&self) -> bool {
        match self {
            Self::Small(x) => *x != 0,
            Self::Big(x) => x.peek() != &BigInt::from(0),
        }
    }

    /// User (not structural) equality does not differentiatie between bignums
    /// and machine integers, even though it should be impossible to create two
    /// distinct representations of the same number, as all arithmetic uses
    /// [`IntVariant::normalize`] as a postprocessing step.
    fn user_eq(&self, other: &IntVariant) -> bool {
        match (self, other) {
            (Self::Small(x), Self::Small(y)) => x.eq(y),
            (Self::Small(x), Self::Big(y)) => y.peek().eq(&BigInt::from(*x)),
            (Self::Big(x), Self::Small(y)) => x.peek().eq(&BigInt::from(*y)),
            (Self::Big(x), Self::Big(y)) => x.eq(y),
        }
    }

    fn format(&self, spec: IntegerFormatSpec) -> Result<String, Error> {
        let base = match (spec.fmt_type, self) {
            (IntegerFormatType::Character, _) => {
                let codepoint = u32::try_from(self).map_err(|_| Error::new(Value::OutOfRange))?;
                let c = char::try_from(codepoint).map_err(|_| Error::new(Value::OutOfRange))?;
                return Ok(c.to_string());
            },
            (IntegerFormatType::Binary, Self::Small(x)) => format!("{:+b}", x),
            (IntegerFormatType::Binary, Self::Big(x)) => format!("{:+b}", x.peek()),
            (IntegerFormatType::Decimal, Self::Small(x)) => format!("{:+}", x),
            (IntegerFormatType::Decimal, Self::Big(x)) => format!("{:+}", x.peek()),
            (IntegerFormatType::Octal, Self::Small(x)) => format!("{:+o}", x),
            (IntegerFormatType::Octal, Self::Big(x)) => format!("{:+o}", x.peek()),
            (IntegerFormatType::Hex(UppercaseSpec::Lower), Self::Small(x)) => format!("{:+x}", x),
            (IntegerFormatType::Hex(UppercaseSpec::Lower), Self::Big(x)) => format!("{:+x}", x.peek()),
            (IntegerFormatType::Hex(UppercaseSpec::Upper), Self::Small(x)) => format!("{:+X}", x),
            (IntegerFormatType::Hex(UppercaseSpec::Upper), Self::Big(x)) => format!("{:+X}", x.peek()),
        };

        let mut base_digits = &base[1..];
        let mut buffer = String::new();

        match (spec.sign, self < &Self::Small(0)) {
            (_, true) => { buffer.push('-'); },
            (SignSpec::Plus, false) => { buffer.push('+'); }
            (SignSpec::Space, false) => { buffer.push(' '); }
            _ => {},
        }

        if spec.alternate {
            match spec.fmt_type {
                IntegerFormatType::Binary => { buffer += "0b"; },
                IntegerFormatType::Octal => { buffer += "0o"; },
                IntegerFormatType::Hex(UppercaseSpec::Lower) => { buffer += "0x"; },
                IntegerFormatType::Hex(UppercaseSpec::Upper) => { buffer += "0X"; },
                _ => {},
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
            Ok(fmt_str(buffer.as_str(), str_spec))
        } else {
            Ok(buffer)
        }
    }
}



// Function variant
// ------------------------------------------------------------------------------------------------

/// A builtin function is a 'pure' function implemented in Rust associated with
/// a name. The name is used for serializing. When deserializing, the name is
/// looked up in the [`BUILTINS`] mapping.
#[derive(Clone)]
pub(crate) struct Builtin {
    /// The rust callable for evaluating the function.
    pub func: fn(&List, Option<&Map>) -> Result<Object, Error>,

    /// The name of the function.
    pub name: Key,
}

// Custom serialization and deserialization logic.

impl Serialize for Builtin {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.name.as_str())
    }
}

struct BuiltinVisitor;

impl<'a> Visitor<'a> for BuiltinVisitor {
    type Value = Builtin;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a string")
    }

    fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
        BUILTINS.get(v).ok_or(E::custom("unknown builtin name")).cloned()
    }
}

impl<'a> Deserialize<'a> for Builtin {
    fn deserialize<D: Deserializer<'a>>(deserializer: D) -> Result<Self, D::Error> where {
        deserializer.deserialize_str(BuiltinVisitor)
    }
}


// /// A function implemented in Gold.
// #[derive(Debug, PartialEq, Serialize, Deserialize, Trace, Finalize)]
// pub(crate) struct Func {
    // /// A pattern for destructuring a list of positional arguments.
    // pub args: ListBinding,

    // /// A pattern for destructuring a map of keyword arguments.
    // pub kwargs: Option<MapBinding>,

    // /// A mapping of captured bindings from the point-of-definition of the
    // /// closure.
    // pub closure: Map,

    // /// A set of names to be resolved later
    // #[unsafe_ignore_trace]
    // pub deferred: Option<HashSet<Key>>,

    // /// The expression to evaluate.
    // pub expr: Tagged<Expr>,
// }


/// A 'pure' function implemented in Rust. Unlike [`Builtin`], this form of
/// function is backed by a dynamic callable object, which can be anything, such
/// as a closure. Such objects can be created dynamically, and are thus
/// necessary for implementing Gold-callable functions in other languages like
/// Python. This also makes them inherently non-serializable.
#[derive(Clone)]
pub(crate) struct Closure(pub(crate) Rc<dyn Fn(&List, Option<&Map>) -> Result<Object, Error>>);


/// The function variant represents all possible forms of callable objects in
/// Gold.
#[derive(Clone, Serialize, Deserialize, Trace, Finalize)]
pub(crate) enum FuncVariant {
    /// Function implemented in Gold.
    Func(Gc<Function>),

    /// Static (serializable) function implemented in Rust.
    Builtin(#[unsafe_ignore_trace] Builtin),

    /// Dynamic (unserializable) function implemented in Rust.
    #[serde(skip)]
    Closure(#[unsafe_ignore_trace] Closure),
}

impl Debug for FuncVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Func(x) => f.debug_tuple("FuncVariant::Func").field(x).finish(),
            Self::Builtin(_) => f.debug_tuple("FuncVariant::Builtin").finish(),
            Self::Closure(_) => f.debug_tuple("FuncVariant::Closure").finish(),
        }
    }
}

impl From<Function> for FuncVariant {
    fn from(value: Function) -> Self {
        FuncVariant::Func(Gc::new(value))
    }
}

impl From<Builtin> for FuncVariant {
    fn from(value: Builtin) -> Self {
        FuncVariant::Builtin(value)
    }
}

impl From<Closure> for FuncVariant {
    fn from(value: Closure) -> Self {
        FuncVariant::Closure(value)
    }
}

impl FuncVariant {
    /// All functions in Gold compare different to each other except built-ins.
    fn user_eq(&self, other: &FuncVariant) -> bool {
        match (self, other) {
            (FuncVariant::Builtin(x), FuncVariant::Builtin(y)) => x.name == y.name,
            _ => false,
        }
    }

    /// Call this function with positional and keyword arguments.
    pub fn call(&self, args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
        Ok(Object::int(0))
        // match self {
        //     Self::Builtin(Builtin { func, .. }) => func(args, kwargs),
        //     Self::Closure(Closure(func)) => func(args, kwargs),
        //     Self::Func(func) => {
        //         let Func { args: fargs, kwargs: fkwargs, closure, expr, .. } = &*func.as_ref().borrow();

        //         // Create a new namespace from the enclosed-over bindings.
        //         let ns = Namespace::Frozen(closure);

        //         // Create a mutable sub-namespace for function parameters.
        //         let mut sub = ns.subtend();

        //         // Bind the positional arguments.
        //         sub.bind_list(&fargs.0, args)?;

        //         // Bind the keyword arguments.
        //         match (fkwargs, kwargs) {
        //             (Some(b), Some(k)) => { sub.bind_map(&b.0, k)?; },
        //             (Some(b), None) => { sub.bind_map(&b.0, &Map::new())?; },
        //             _ => {},
        //         }

        //         // Evaluate the function.
        //         sub.eval(expr)
        //     }
        // }
    }

    pub(crate) fn resolve_deferred(&self, ns: &Namespace) -> Result<(), Error> {
        Ok(())
        // match self {
        //     Self::Func(func) => {
        //         if let Func { closure, deferred: Some(deferred), .. } = &mut *func.as_ref().borrow_mut() {
        //             for name in deferred.iter() {
        //                 closure.insert(*name, ns.get_immediate(name)?);
        //             }
        //         }
        //         Ok(())
        //     }
        //     _ => Ok(()),
        // }
    }
}



// Object variant
// ------------------------------------------------------------------------------------------------

/// The object variant implements all possible variants of Gold objects,
/// although it's not the user-facing type, which is [`Object`], an opaque
/// struct enclosing an `ObjectVariant`.
#[derive(Clone, Debug, Serialize, Deserialize, Trace, Finalize)]
pub(crate) enum ObjectVariant {
    /// Integers
    Int(IntVariant),

    /// Floating-point numbers
    Float(f64),

    /// Strings
    Str(StrVariant),

    /// Booleans
    Boolean(bool),

    /// Lists
    List(Gc<GcCell<List>>),

    /// Mappings
    Map(Gc<GcCell<Map>>),

    /// Functions
    Func(FuncVariant),

    /// Null
    Null,
}

// FuncVariant doesn't implement PartialEq, so this has to be done manually.
impl PartialEq<ObjectVariant> for ObjectVariant {
    fn eq(&self, other: &ObjectVariant) -> bool {
        match (self, other) {
            (Self::Int(x), Self::Int(y)) => x.eq(y),
            (Self::Float(x), Self::Float(y)) => x.eq(y),
            (Self::Str(x), Self::Str(y)) => x.eq(y),
            (Self::Boolean(x), Self::Boolean(y)) => x.eq(y),
            (Self::List(x), Self::List(y)) => x.eq(y),
            (Self::Map(x), Self::Map(y)) => x.eq(y),
            (Self::Null, Self::Null) => true,
            _ => false,
        }
    }
}

impl PartialOrd<ObjectVariant> for ObjectVariant {
    fn partial_cmp(&self, other: &ObjectVariant) -> Option<Ordering> {
        match (self, other) {
            (Self::Int(x), Self::Int(y)) => x.partial_cmp(y),
            (Self::Int(x), Self::Float(y)) => x.partial_cmp(y),
            (Self::Float(_), Self::Int(_)) => other.partial_cmp(self).map(Ordering::reverse),
            (Self::Float(x), Self::Float(y)) => x.partial_cmp(y),
            (Self::Str(x), Self::Str(y)) => x.partial_cmp(y),
            _ => None,
        }
    }
}

impl ObjectVariant {
    /// Get the type of this object.
    pub fn type_of(&self) -> Type {
        match self {
            Self::Int(_) => Type::Integer,
            Self::Float(_) => Type::Float,
            Self::Str(_) => Type::String,
            Self::Boolean(_) => Type::Boolean,
            Self::List(_) => Type::List,
            Self::Map(_) => Type::Map,
            Self::Func(_) => Type::Function,
            Self::Null => Type::Null,
        }
    }

    /// Construct a list.
    pub fn list<T>(x: T) -> Self where T: ToVec<Object> {
        Self::List(Gc::new(GcCell::new(x.to_vec())))
    }

    /// Construct a map.
    pub fn map<T>(x: T) -> Self where T: ToMap<Key, Object> {
        Self::Map(Gc::new(GcCell::new(x.to_map())))
    }

    /// Normalize an integer variant, converting bignums to machine integers if
    /// they fit.
    pub fn numeric_normalize(&self) -> Self {
        if let Self::Int(x) = self {
            Self::Int(x.normalize())
        } else {
            self.clone()
        }
    }

    /// String representation of this object. Used for string interpolation.
    pub fn format(&self, spec: FormatSpec) -> Result<String, Error> {
        match self {
            Self::Str(r) => {
                if let Some(str_spec) = spec.string_spec() {
                    Ok(fmt_str(r.as_str(), str_spec))
                } else {
                    Err(Error::new(TypeMismatch::InterpolateSpec(self.type_of())))
                }
            },
            Self::Boolean(x) => {
                if let Some(str_spec) = spec.string_spec() {
                    let s = if *x { "true" } else { "false" };
                    Ok(fmt_str(s, str_spec))
                } else if let Some(int_spec) = spec.integer_spec() {
                    let i = if *x { 1 } else { 0 };
                    IntVariant::Small(i).format(int_spec)
                } else if let Some(float_spec) = spec.float_spec() {
                    let f = if *x { 1.0 } else { 0.0 };
                    Ok(fmt_float(f, float_spec))
                } else {
                    Err(Error::new(TypeMismatch::InterpolateSpec(self.type_of())))
                }
            },
            Self::Null => {
                if let Some(str_spec) = spec.string_spec() {
                    Ok(fmt_str("null", str_spec))
                } else {
                    Err(Error::new(TypeMismatch::InterpolateSpec(self.type_of())))
                }
            },
            Self::Int(r) => {
                if let Some(int_spec) = spec.integer_spec() {
                    r.format(int_spec)
                } else if let Some(float_spec) = spec.float_spec() {
                    Ok(fmt_float(r.to_f64(), float_spec))
                } else {
                    Err(Error::new(TypeMismatch::InterpolateSpec(self.type_of())))
                }
            },
            Self::Float(r) => {
                if let Some(float_spec) = spec.float_spec() {
                    Ok(fmt_float(*r, float_spec))
                } else {
                    Err(Error::new(TypeMismatch::InterpolateSpec(self.type_of())))
                }
            },
            _ => Err(Error::new(TypeMismatch::Interpolate(self.type_of()))),
        }
    }

    /// Mathematical negation.
    pub fn neg(&self) -> Result<Self, Error> {
        match self {
            Self::Int(x) => Ok(Self::Int(x.neg())),
            Self::Float(x) => Ok(Self::Float(-x)),
            _ => Err(Error::new(TypeMismatch::UnOp(self.type_of(), UnOp::ArithmeticalNegate))),
        }
    }

    /// The plus operator: concatenate strings and lists, or delegate to mathematical addition.
    pub fn add(&self, other: &Self) -> Result<Self, Error> {
        match (&self, &other) {
            (Self::List(x), Self::List(y)) => Ok(Self::list(x.borrow().iter().chain(y.borrow().iter()).map(Object::clone).collect::<List>())),
            (Self::Str(x), Self::Str(y)) => Ok(Self::Str(x.add(y))),
            _ => self.operate(other, IntVariant::add, |x,y| x + y, BinOp::Add),
        }
    }

    /// The minus operator: mathematical subtraction.
    pub fn sub(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, IntVariant::sub, |x,y| x - y, BinOp::Subtract)
    }

    /// The asterisk operator: mathematical multiplication.
    pub fn mul(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, IntVariant::mul, |x,y| x * y, BinOp::Multiply)
    }

    /// The slash operator: mathematical division.
    pub fn div(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, IntVariant::div, |x,y| x / y, BinOp::Divide)
    }

    /// The double slash operator: integer division.
    pub fn idiv(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, IntVariant::idiv, |x,y| (x / y).floor() as f64, BinOp::IntegerDivide)
    }

    /// Universal utility method for implementing mathematical operators.
    ///
    /// If both operands are integer variants, the `ixi` function is applied. If
    /// either operand is not an integer, both operands are converted to floats
    /// and the `fxf` function is applied.
    ///
    /// In case of type mismatch, an error is reported using `op`.
    fn operate<S,T>(
        &self,
        other: &Self,
        ixi: impl Fn(&IntVariant, &IntVariant) -> S,
        fxf: impl Fn(f64, f64) -> T,
        op: BinOp
    ) -> Result<Self, Error> where
        Self: From<S> + From<T>,
    {
        match (self, other) {
            (Self::Int(xx), Self::Int(yy)) => Ok(Self::from(ixi(xx, yy))),
            (Self::Int(xx), Self::Float(yy)) => Ok(Self::from(fxf(xx.to_f64(), *yy))),
            (Self::Float(xx), Self::Int(yy)) => Ok(Self::from(fxf(*xx, yy.to_f64()))),
            (Self::Float(xx), Self::Float(yy)) => Ok(Self::from(fxf(*xx, *yy))),

            _ => Err(Error::new(TypeMismatch::BinOp(self.type_of(), other.type_of(), op))),
        }
    }

    /// The exponentiation operator. This uses [`IntVariant::pow`] if both
    /// operands are integers and if the exponent is non-negative. Otherwise it
    /// delegates to floating-point exponentiation.
    pub fn pow(&self, other: &Self) -> Result<Self, Error> {
        if let (Self::Int(x), Self::Int(y)) = (self, other) {
            if let Some(r) = x.pow(y) {
                return Ok(Self::from(r));
            }
        }

        let (xx, yy) = self.to_f64()
            .and_then(|x| other.to_f64().map(|y| (x, y)))
            .ok_or_else(|| Error::new(TypeMismatch::BinOp(self.type_of(), other.type_of(), BinOp::Power)))?;
        Ok(Self::from(xx.powf(yy)))
    }

    /// The containment operator.
    pub fn contains(&self, other: &Object) -> Result<bool, Error> {
        if let Self::List(x) = self {
            return Ok(x.borrow().contains(other));
        }

        if let (Self::Str(haystack), Self::Str(needle)) = (self, &other.0) {
            return Ok(haystack.as_str().contains(needle.as_str()));
        }

        Err(Error::new(TypeMismatch::BinOp(self.type_of(), other.type_of(), BinOp::Contains)))
    }

    /// Convert to f64 if possible.
    pub fn to_f64(&self) -> Option<f64> {
        match self {
            Self::Int(x) => Some(x.to_f64()),
            Self::Float(x) => Some(*x),
            _ => None,
        }
    }

    /// Resolve deferred bindings.
    pub(crate) fn resolve_deferred(&self, ns: &Namespace) -> Result<(), Error> {
        match self {
            Self::Func(func) => func.resolve_deferred(ns),
            _ => Ok(()),
        }
    }
}

impl<T> From<T> for ObjectVariant where IntVariant: From<T> {
    fn from(value: T) -> Self {
        Self::Int(IntVariant::from(value))
    }
}

impl From<f64> for ObjectVariant {
    fn from(x: f64) -> Self { Self::Float(x) }
}

impl Display for ObjectVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Str(r) => f.write_fmt(format_args!("{}", r)),
            Self::Int(r) => f.write_fmt(format_args!("{}", r)),
            Self::Float(r) => f.write_fmt(format_args!("{}", r)),
            Self::Boolean(true) => f.write_str("true"),
            Self::Boolean(false) => f.write_str("false"),
            Self::Null => f.write_str("null"),

            Self::List(elements) => {
                f.write_str("[")?;
                let temp = elements.borrow();
                let mut iter = temp.iter().peekable();
                while let Some(element) = iter.next() {
                    f.write_fmt(format_args!("{}", element))?;
                    if iter.peek().is_some() {
                        f.write_str(", ")?;
                    }
                }
                f.write_str("]")
            }

            Self::Map(elements) => {
                f.write_str("{")?;
                let temp = elements.borrow();
                let mut iter = temp.iter().peekable();
                while let Some((k, v)) = iter.next() {
                    f.write_fmt(format_args!("{}: {}", k, v))?;
                    if iter.peek().is_some() {
                        f.write_str(", ")?;
                    }
                }
                f.write_str("}")
            }

            _ => f.write_str("?"),
        }
    }
}

impl TryFrom<&ObjectVariant> for JsonValue {
    type Error = Error;

    fn try_from(value: &ObjectVariant) -> Result<Self, Self::Error> {
        match value {
            ObjectVariant::Int(x) => i64::try_from(x).map_err(|_| Error::new(Value::TooLarge)).map(JsonValue::from),
            ObjectVariant::Float(x) => Ok(JsonValue::from(*x)),
            ObjectVariant::Str(x) => Ok(JsonValue::from(x.as_str())),
            ObjectVariant::Boolean(x) => Ok(JsonValue::from(*x)),
            ObjectVariant::List(x) => {
                let mut val = JsonValue::new_array();
                for element in x.borrow().iter() {
                    val.push(JsonValue::try_from(element.clone())?).unwrap();
                }
                Ok(val)
            },
            ObjectVariant::Map(x) => {
                let mut val = JsonValue::new_object();
                for (key, element) in x.borrow().iter() {
                    val[key.as_str()] = JsonValue::try_from(element.clone())?;
                }
                Ok(val)
            },
            ObjectVariant::Null => Ok(JsonValue::Null),
            _ => Err(Error::new(TypeMismatch::Json(value.type_of()))),
        }
    }
}



// Utility macro for wrapping a unary operator.
macro_rules! wrap1 {
    ($name:ident) => {
        #[doc=concat!("Wrapper for [`ObjectVariant::", stringify!($name), "`]")]
        pub fn $name(&self) -> Result<Self, Error> {
            self.0.$name().map(Self)
        }
    };
}


// Utility macro for wrapping a binary operator.
macro_rules! wrap2 {
    ($name:ident) => {
        #[doc=concat!("Wrapper for [`ObjectVariant::", stringify!($name), "`]")]
        pub fn $name(&self, other: &Self) -> Result<Self, Error> {
            self.0.$name(&other.0).map(Self)
        }
    };
}


// Utility macro for extracting a certain type from an object variant. Used for
// facilitating writing Gold functions in Rust.
macro_rules! extract {
    ($index:expr , $args:ident , str) => { $args.get($index).and_then(|x| x.get_str()) };
    ($index:expr , $args:ident , int) => { $args.get($index).and_then(|x| x.get_int()) };
    ($index:expr , $args:ident , float) => { $args.get($index).and_then(|x| x.get_float()) };
    ($index:expr , $args:ident , bool) => { $args.get($index).and_then(|x| x.get_bool()) };
    ($index:expr , $args:ident , list) => { $args.get($index).and_then(|x| x.get_list()) };
    ($index:expr , $args:ident , map) => { $args.get($index).and_then(|x| x.get_map()) };
    ($index:expr , $args:ident , func) => { $args.get($index).and_then(|x| x.get_func()) };
    ($index:expr , $args:ident , null) => { $args.get($index).and_then(|x| x.get_null()) };

    ($index:expr , $args:ident , any) => { $args.get($index) };

    ($index:expr , $args:ident , tofloat) => {
        $args.get($index).and_then(|x| x.get_float()).or_else(
            || $args.get($index).and_then(|x| x.get_int().map(|x| x.to_f64()))
        )
    };
}


macro_rules! extractkw {
    ($kwargs:ident , $key:ident , any) => { $kwargs.and_then(|kws| kws.get(&$crate::object::Key::from(stringify!($key)))) };

    ($kwargs:ident , $key:ident , tofloat) => {{
        let key = $crate::object::Key::from(stringify!($key));
        $kwargs.and_then(
            |kws| kws.get(&key).and_then(|x| x.get_float()).or_else(
                || kws.get(&key).and_then(|x| x.get_int().map(|x| x.to_f64()))
            )
        )
    }};
}


/// Utility macro for capturing a certain calling convention. Used for writing
/// Gold functions in Rust.
///
/// ```ignore
/// signature!(args = [x: int, y: float] {
///     // function body
/// })
/// ```
///
/// The function body is executed if the list `args` matches the given types.
/// The number and types of the arguments must be exact. If the arguments don't
/// match, or if the function body does not return, evaluation proceeds. You can
/// therefore call this macro multiple times in succession to match different
/// calling conventions.
#[macro_export]
macro_rules! signature {
    // Entry point pattern
    ($args:ident = [ $($param:ident : $type:ident),* ] $kwargs:ident = { $($kw:ident : $kwtype:ident),* } $block:block) => {
        signature!(0 ; $args [ $($param : $type),* ] , $kwargs [ $($kw : $kwtype),* ] , $block)
    };

    // Entry point pattern, no kwargs
    ($args:ident = [ $($param:ident : $type:ident),* ] $block:block) => {
        signature!(0 ; $args [ $($param : $type),* ] , missing [ ] , $block)
    };

    ($index:expr ; $args:ident [ $param:ident : $type:ident , $($params:ident : $types:ident),+ ] , $kwargs:ident [ $($kw:ident : $kwtype:ident),* ] , $block:block) => {
        if let Some($param) = extract!($index, $args, $type) {
            signature!($index + 1 ; $args [ $($params : $types),* ] , $kwargs [ $($kw : $kwtype),* ] , $block)
        }
    };

    ($index:expr ; $args:ident [ $param:ident : $type:ident ] , $kwargs:ident [ $($kw:ident : $kwtype:ident),* ] , $block:block) => {
        if let Some($param) = extract!($index, $args, $type) {
            signature!($index + 1 ; $args [ ] , $kwargs [ $($kw : $kwtype),* ] , $block)
        }
    };

    ($index:expr ; $args:ident [ ] , $kwargs:ident [ $kw:ident : $kwtype:ident ($kws:ident : $kwtypes:ident),+ ] , $block:block) => {
        if let Some($kw) = extractkw!($kwargs, $kw, $kwtype) {
            signature!($index ; $args [ ] , $kwargs [ $($kws : $kwtypes),* ] , $block)
        }
    };

    ($index:expr ; $args:ident [ ] , $kwargs:ident [ $kw:ident : $kwtype:ident ] , $block:block) => {
        if let Some($kw) = extractkw!($kwargs, $kw, $kwtype) {
            signature!($index ; $args [ ] , $kwargs [ ] , $block)
        }
    };

    ($index:expr ; $args:ident [ ] , $kwargs:ident [ ] , $block:block) => {
        if $args.len() == $index $block
    };
}

pub use signature;



// Object
// ------------------------------------------------------------------------------------------------

/// The general type of Gold objects.
///
/// While this type wraps [`ObjectVariant`], a fact which can be revealed using
/// the [`Object::variant`] method, this should be considered an implementation
/// detail.
///
/// `Object` is `Deref<ObjectVariant>`, so supports all methods defined there.
#[derive(Clone, Debug, PartialEq, PartialOrd, Serialize, Deserialize, Trace, Finalize)]
pub struct Object(pub(crate) ObjectVariant);

impl Object {
    /// Construct an interned string.
    pub fn str_interned(val: impl AsRef<str>) -> Self {
        Self(ObjectVariant::Str(StrVariant::interned(val)))
    }

    /// Construct a non-interned string.
    pub fn str_natural(val: impl AsRef<str>) -> Self {
        Self(ObjectVariant::Str(StrVariant::natural(val)))
    }

    /// Construct a string, deciding based on length whether to intern or not.
    pub fn str(val: impl AsRef<str>) -> Self {
        if val.as_ref().len() < 20 {
            Self::str_interned(val)
        } else {
            Self::str_natural(val)
        }
    }

    /// Construct a string directly from an interned symbol.
    pub fn key(val: Key) -> Self {
        Self(ObjectVariant::Str(StrVariant::Interned(val)))
    }

    /// Construct an integer.
    pub(crate) fn int<T>(val: T) -> Self
    where
        IntVariant: From<T>
    {
        Self(ObjectVariant::Int(IntVariant::from(val)))
    }

    /// Construct a big integer from a decimal string representation.
    pub fn bigint(x: impl AsRef<str>) -> Option<Self> {
        BigInt::from_str(x.as_ref()).ok().map(|x| Self(ObjectVariant::from(x).numeric_normalize()))
    }

    /// Construct a float.
    pub fn float(val: f64) -> Self {
        Self(ObjectVariant::Float(val))
    }

    /// Construct a boolean.
    pub fn bool(val: bool) -> Self {
        Self(ObjectVariant::Boolean(val))
    }

    /// Return the null object.
    pub fn null() -> Self {
        Self(ObjectVariant::Null)
    }

    /// Construct a function.
    pub(crate) fn func<T>(val: T) -> Self
    where
        FuncVariant: From<T>
    {
        Self(ObjectVariant::Func(FuncVariant::from(val)))
    }

    /// Construct a list.
    pub fn list(x: impl ToVec<Object>) -> Self {
        Self(ObjectVariant::list(x))
    }

    /// Construct an empty list.
    pub fn new_list() -> Self {
        Self(ObjectVariant::List(Gc::new(GcCell::new(vec![]))))
    }

    /// Construct a map.
    pub(crate) fn map(x: impl ToMap<Key, Object>) -> Self {
        Self(ObjectVariant::map(x))
    }

    /// Construct an empty map.
    pub fn new_map() -> Self {
        Self(ObjectVariant::Map(Gc::new(GcCell::new(Map::new()))))
    }

    /// Serialize this objcet to a byte vector.
    pub fn serialize(&self) -> Option<Vec<u8>> {
        let data = (SERIALIZE_VERSION, SystemTime::now(), self);
        encode::to_vec(&data).ok()
    }

    /// Serialize this objcet to a writable buffer.
    pub fn serialize_write<T: Write + ?Sized>(&self, out: &mut T) -> Option<()> {
        let data = (SERIALIZE_VERSION, SystemTime::now(), self);
        encode::write(out, &data).ok()
    }

    /// Deserialize an object from a byte vector.
    pub fn deserialize(data: &Vec<u8>) -> Option<(Self, SystemTime)> {
        let (version, time, retval) = decode::from_slice::<(i32, SystemTime, Self)>(data.as_slice()).ok()?;
        if version < SERIALIZE_VERSION {
            None
        } else {
            Some((retval, time))
        }
    }

    /// Deserialize an object from a readable buffer.
    pub fn deserialize_read<T: Read>(data: T) -> Option<(Self, SystemTime)> {
        let (version, time, retval) = decode::from_read::<T, (i32, SystemTime, Self)>(data).ok()?;
        if version < SERIALIZE_VERSION {
            None
        } else {
            Some((retval, time))
        }
    }

    /// Get the type of this object.
    pub fn type_of(&self) -> Type {
        self.0.type_of()
    }

    /// User-facing (non-structural) equality.
    ///
    /// We use a stricter form of equality checking for testing purposes. This
    /// method implements equality under Gold semantics.
    pub fn user_eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            // Equality between disparate types
            (ObjectVariant::Float(x), ObjectVariant::Int(y)) => y.eq(x),
            (ObjectVariant::Int(x), ObjectVariant::Float(y)) => x.eq(y),

            // Structural equality
            (ObjectVariant::Int(x), ObjectVariant::Int(y)) => x.user_eq(y),
            (ObjectVariant::Float(x), ObjectVariant::Float(y)) => x.eq(y),
            (ObjectVariant::Str(x), ObjectVariant::Str(y)) => x.user_eq(y),
            (ObjectVariant::Boolean(x), ObjectVariant::Boolean(y)) => x.eq(y),
            (ObjectVariant::Null, ObjectVariant::Null) => true,
            (ObjectVariant::Func(x), ObjectVariant::Func(y)) => x.user_eq(y),

            // Composite objects: we must implement equality the hard way, since
            // `eq` would not delegate to checking contained objects using
            // `user_eq`.
            (ObjectVariant::List(x), ObjectVariant::List(y)) => {
                let xx = x.borrow();
                let yy = y.borrow();
                if xx.len() != yy.len() {
                    return false;
                }
                for (xx, yy) in xx.iter().zip(yy.iter()) {
                    if !xx.user_eq(yy) {
                        return false
                    }
                }
                true
            },

            (ObjectVariant::Map(x), ObjectVariant::Map(y)) => {
                let xx = x.borrow();
                let yy = y.borrow();
                if xx.len() != yy.len() {
                    return false
                }
                for (xk, xv) in xx.iter() {
                    if let Some(yv) = yy.get(xk) {
                        if !xv.user_eq(yv) {
                            return false
                        }
                    } else {
                        return false
                    }
                }
                true
            },

            // Different types generally mean not equal
            _ => false,
        }
    }

    /// Extract the string variant if applicable.
    pub fn get_str(&self) -> Option<&str> {
        match &self.0 {
            ObjectVariant::Str(x) => Some(x.as_str()),
            _ => None,
        }
    }

    /// Extract the integer variant if applicable.
    pub(crate) fn get_int(&self) -> Option<&IntVariant> {
        match &self.0 {
            ObjectVariant::Int(x) => Some(x),
            _ => None,
        }
    }

    /// Extract the floating-point variant if applicable.
    pub fn get_float(&self) -> Option<f64> {
        match &self.0 {
            ObjectVariant::Float(x) => Some(*x),
            _ => None,
        }
    }

    /// Extract the bool variant if applicable. (See also [`ObjectVariant::truthy`].)
    pub fn get_bool(&self) -> Option<bool> {
        match &self.0 {
            ObjectVariant::Boolean(x) => Some(*x),
            _ => None,
        }
    }

    /// Extract the list variant if applicable.
    pub fn get_list<'a>(&'a self) -> Option<GcCellRef<'_, List>> {
        match &self.0 {
            ObjectVariant::List(x) => Some(x.borrow()),
            _ => None
        }
    }

    /// Extract the map variant if applicable.
    pub(crate) fn get_map<'a>(&'a self) -> Option<GcCellRef<'_, Map>> {
        match &self.0 {
            ObjectVariant::Map(x) => Some(x.borrow()),
            _ => None
        }
    }

    /// Extract the key variant if applicable (an interned string).
    pub fn get_key(&self) -> Option<Key> {
        match &self.0 {
            ObjectVariant::Str(x) => Some(Key::from(x)),
            _ => None,
        }
    }

    /// Extract the function variant if applicable.
    pub(crate) fn get_func(&self) -> Option<&FuncVariant> {
        match &self.0 {
            ObjectVariant::Func(x) => Some(x),
            _ => None,
        }
    }

    /// Extract the null variant if applicable.
    ///
    /// Note that `obj.get_null().is_some() == obj.is_null()`.
    pub fn get_null(&self) -> Option<()> {
        match &self.0 {
            ObjectVariant::Null => Some(()),
            _ => None,
        }
    }

    /// Check whether the object is null.
    pub fn is_null(&self) -> bool {
        match &self.0 {
            ObjectVariant::Null => true,
            _ => false,
        }
    }

    /// The function call operator.
    pub(crate) fn call(&self, args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
        match &self.0 {
            ObjectVariant::Func(func) => func.call(args, kwargs),
            _ => Err(Error::new(TypeMismatch::Call(self.type_of()))),
        }
    }

    /// Check whether this object is truthy, as interpreted by if-then-else
    /// expressions.
    ///
    /// Every object is truthy except for null, false and zeros. In particular,
    /// empty collections are truthy!
    pub fn truthy(&self) -> bool {
        match &self.0 {
            ObjectVariant::Null => false,
            ObjectVariant::Boolean(val) => *val,
            ObjectVariant::Int(r) => r.nonzero(),
            ObjectVariant::Float(r) => *r != 0.0,
            _ => true,
        }
    }

    /// Return `Some(true)` if `self` and `other` are comparable and that the
    /// comparison is equal to `ordering`. Returns `Some(false)` if it is not.
    /// Returns `None` if they are not comparable.
    pub fn cmp_bool(&self, other: &Self, ordering: Ordering) -> Option<bool> {
        self.0.partial_cmp(&other.0).map(|x| x == ordering)
    }

    /// The indexing operator (for both lists and maps).
    pub fn index(&self, other: &Object) -> Result<Object, Error> {
        match (&self.0, &other.0) {
            (ObjectVariant::List(x), ObjectVariant::Int(y)) => {
                let xx = x.borrow();
                let i: usize = y.try_into().map_err(|_| Error::new(Value::OutOfRange))?;
                if i >= xx.len() {
                    Err(Error::new(Value::OutOfRange))
                } else {
                    Ok(xx[i].clone())
                }
            }
            (ObjectVariant::Map(x), ObjectVariant::Str(y)) => {
                let xx = x.borrow();
                let yy = GlobalSymbol::from(y);
                xx.get(&yy).ok_or_else(|| Error::new(Reason::Unassigned(yy))).map(Object::clone)
            }
            _ => Err(Error::new(TypeMismatch::BinOp(self.type_of(), other.type_of(), BinOp::Index))),
        }
    }

    /// Wrap [`ObjectVariant::resolve_deferred`]
    pub(crate) fn resolve_deferred(&self, ns: &Namespace) -> Result<(), Error> {
        self.0.resolve_deferred(ns)
    }

    /// Wrap [`ObjectVariant::format`].
    pub fn format(&self, spec: FormatSpec) -> Result<String, Error> {
        self.0.format(spec)
    }

    /// Wrap [`ObjectVariant::numeric_normalize`].
    pub fn numeric_normalize(self) -> Self {
        Self(self.0.numeric_normalize())
    }

    /// Wrap [`ObjectVariant::contains`].
    pub fn contains(self, other: &Self) -> Result<bool, Error> {
        self.0.contains(other)
    }

    // Auto-wrap some unary and binary operators.
    wrap1!{neg}
    wrap2!{add}
    wrap2!{sub}
    wrap2!{mul}
    wrap2!{div}
    wrap2!{idiv}
    wrap2!{pow}
}

impl FromIterator<Object> for Object {
    fn from_iter<T: IntoIterator<Item = Object>>(iter: T) -> Self {
        Object(ObjectVariant::List(Gc::new(GcCell::new(iter.into_iter().collect()))))
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{}", self.0))
    }
}

impl TryFrom<Object> for JsonValue {
    type Error = Error;

    fn try_from(value: Object) -> Result<Self, Self::Error> {
        Self::try_from(&value.0)
    }
}

impl From<bool> for Object {
    fn from(value: bool) -> Self {
        Object::bool(value)
    }
}

impl From<i32> for Object {
    fn from(value: i32) -> Self {
        Object::int(value)
    }
}

impl From<i64> for Object {
    fn from(value: i64) -> Self {
        Object::int(value)
    }
}

impl From<f64> for Object {
    fn from(value: f64) -> Self {
        Object::float(value)
    }
}

impl From<&str> for Object {
    fn from(value: &str) -> Self {
        Object::str(value)
    }
}

impl From<Key> for Object {
    fn from(value: Key) -> Self {
        Object::key(value)
    }
}
