use std::cmp::Ordering;
use std::fmt::{Debug, Display};
use std::io::{Read, Write};
use std::iter::Step;
use std::ops::Deref;
use std::str::FromStr;
use std::sync::Arc;
use std::time::SystemTime;

use indexmap::IndexMap;
use json::JsonValue;
use num_bigint::{BigInt, BigUint};
use num_traits::{ToPrimitive, checked_pow};
use rmp_serde::{decode, encode};
use serde::de::Visitor;
use serde::{Serialize, Serializer, Deserialize, Deserializer};
use symbol_table::GlobalSymbol;

use crate::builtins::BUILTINS;
use crate::traits::{ToVec, ToMap};

use crate::ast::{ListBinding, MapBinding, Expr, BinOp, UnOp};
use crate::error::{Error, Tagged, TypeMismatch, Value, Reason};
use crate::eval::Namespace;
use crate::util;


// A Gold object is represented by the



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


#[derive(Clone, Serialize, Deserialize, PartialEq, Debug)]
pub enum StrVariant {
    Interned(Key),
    Natural(Arc<String>),
}

impl PartialOrd<StrVariant> for StrVariant {
    fn partial_cmp(&self, other: &StrVariant) -> Option<Ordering> {
        self.as_str().partial_cmp(other.as_str())
    }
}

impl From<&StrVariant> for GlobalSymbol {
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
    pub fn interned<T: AsRef<str>>(x: T) -> Self {
        Self::Interned(Key::new(x))
    }

    pub fn natural<T: AsRef<str>>(x: T) -> Self {
        Self::Natural(Arc::new(x.as_ref().to_string()))
    }

    pub fn as_str(&self) -> &str {
        match self {
            Self::Interned(x) => x.as_str(),
            Self::Natural(x) => x.as_str(),
        }
    }

    fn format(&self) -> String {
        self.as_str().to_string()
    }

    fn user_eq(&self, other: &StrVariant) -> bool {
        match (self, other) {
            (Self::Interned(x), Self::Interned(y)) => x == y,
            (Self::Natural(x), Self::Interned(y)) => x.as_str() == y.as_str(),
            (Self::Interned(x), Self::Natural(y)) => x.as_str() == y.as_str(),
            (Self::Natural(x), Self::Natural(y)) => x.as_str() == y.as_str(),
        }
    }

    fn add(&self, other: &StrVariant) -> StrVariant {
        Self::natural(format!("{}{}", self.as_str(), other.as_str()))
    }
}



// Integer variant
// ------------------------------------------------------------------------------------------------


#[derive(Clone, Serialize, Deserialize, PartialEq, Debug)]
pub enum IntVariant {
    Small(i64),
    Big(Arc<BigInt>),
}

impl PartialOrd<IntVariant> for IntVariant {
    fn partial_cmp(&self, other: &IntVariant) -> Option<Ordering> {
        match (self, other) {
            (Self::Small(x), Self::Small(y)) => x.partial_cmp(y),
            (Self::Small(x), Self::Big(y)) => BigInt::from(*x).partial_cmp(y),
            (Self::Big(x), Self::Small(y)) => x.as_ref().partial_cmp(&BigInt::from(*y)),
            (Self::Big(x), Self::Big(y)) => x.as_ref().partial_cmp(y.as_ref()),
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
                let (lo, hi) = util::f64_to_bigs(*other);
                if x.as_ref() < &lo || x.as_ref() == &lo && lo != hi {
                    Some(Ordering::Less)
                } else if x.as_ref() > &hi || x.as_ref() == &hi && lo != hi {
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
        Self::Big(Arc::new(value))
    }
}

impl From<&i64> for IntVariant {
    fn from(x: &i64) -> Self {
        Self::Small(*x)
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
            IntVariant::Big(x) => Self::try_from(x.as_ref()).map_err(|_| ()),
        }
    }
}

impl TryFrom<&IntVariant> for i64 {
    type Error = ();

    fn try_from(value: &IntVariant) -> Result<Self, Self::Error> {
        match value {
            IntVariant::Small(x) => Ok(*x),
            IntVariant::Big(x) => Self::try_from(x.as_ref()).map_err(|_| ()),
        }
    }
}

impl TryFrom<&IntVariant> for usize {
    type Error = ();

    fn try_from(value: &IntVariant) -> Result<Self, Self::Error> {
        match value {
            IntVariant::Small(x) => Self::try_from(*x).map_err(|_| ()),
            IntVariant::Big(x) => Self::try_from(x.as_ref()).map_err(|_| ()),
        }
    }
}

impl Display for IntVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Small(r) => f.write_fmt(format_args!("{}", r)),
            Self::Big(r) => f.write_fmt(format_args!("{}", r)),
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
    fn add(&self, other: &IntVariant) -> IntVariant {
        IntVariant::normalize(self.operate(other, i64::checked_add, |x,y| x + y))
    }

    fn sub(&self, other: &IntVariant) -> IntVariant {
        IntVariant::normalize(self.operate(other, i64::checked_sub, |x,y| x - y))
    }

    fn mul(&self, other: &IntVariant) -> IntVariant {
        IntVariant::normalize(self.operate(other, i64::checked_mul, |x,y| x * y))
    }

    fn div(&self, other: &IntVariant) -> f64 {
        self.operate(
            other,
            |x,y| Some((x as f64) / (y as f64)),
            |x,y| util::big_to_f64(x) / util::big_to_f64(y),
        )
    }

    fn idiv(&self, other: &IntVariant) -> IntVariant {
        IntVariant::normalize(self.operate(other, i64::checked_div, |x,y| x / y))
    }

    fn operate<F,G,S,T,U>(&self, other: &IntVariant, ixi: F, bxb: G) -> U
    where
        F: Fn(i64, i64) -> Option<S>,
        G: Fn(&BigInt, &BigInt) -> T,
        U: From<S> + From<T>,
    {
        match (self, other) {
            (Self::Small(xx), Self::Small(yy)) => ixi(*xx, *yy).map(U::from).unwrap_or_else(
                || U::from(bxb(&BigInt::from(*xx), &BigInt::from(*yy)))
            ),
            (Self::Small(xx), Self::Big(yy)) => U::from(bxb(&BigInt::from(*xx), yy.as_ref())),
            (Self::Big(xx), Self::Small(yy)) => U::from(bxb(xx.as_ref(), &BigInt::from(*yy))),
            (Self::Big(xx), Self::Big(yy)) => U::from(bxb(xx.as_ref(), yy.as_ref())),
        }
    }

    fn neg(&self) -> IntVariant {
        match self {
            Self::Small(x) => {
                if let Some(y) = x.checked_neg() {
                    Self::Small(y)
                } else {
                    Self::from(-BigInt::from(*x)).normalize()
                }
            },
            Self::Big(x) => Self::from(-x.as_ref()).normalize(),
        }
    }

    fn small_pow(&self, other: &IntVariant) -> Option<IntVariant> {
        if let (Self::Small(x), Self::Small(y)) = (self, other) {
            let yy: usize = (*y).try_into().ok()?;
            checked_pow(*x, yy).map(Self::from)
        } else {
            None
        }
    }

    fn medium_pow(&self, other: &IntVariant) -> Option<IntVariant> {
        let yy: u32 = other.try_into().ok()?;

        match self {
            Self::Big(x) => Some(Self::from(x.pow(yy))),
            Self::Small(x) => Some(Self::from(BigInt::from(*x).pow(yy))),
        }
    }

    fn big_pow(&self, other: &IntVariant) -> Option<IntVariant> {
        if other.eq(&IntVariant::from(0)) {
            return Some(IntVariant::from(1));
        }

        let mut exp = match other {
            Self::Small(x) => BigUint::try_from(*x).ok()?,
            Self::Big(x) => BigUint::try_from(x.as_ref().clone()).ok()?,
        };

        let mut base = match self {
            Self::Small(x) => BigInt::from(*x),
            Self::Big(x) => x.as_ref().clone(),
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

    fn pow(&self, other: &IntVariant) -> Option<IntVariant> {
        self.small_pow(other)
            .or_else(|| self.medium_pow(other))
            .or_else(|| self.big_pow(other))
    }

    fn normalize(self) -> IntVariant {
        if let Self::Big(x) = &self {
            x.to_i64().map(IntVariant::Small).unwrap_or(self)
        } else {
            self
        }
    }

    pub fn to_f64(&self) -> f64 {
        match self {
            Self::Small(x) => *x as f64,
            Self::Big(x) => util::big_to_f64(x.as_ref()),
        }
    }

    fn nonzero(&self) -> bool {
        match self {
            Self::Small(x) => *x != 0,
            Self::Big(x) => x.as_ref() != &BigInt::from(0),
        }
    }

    fn user_eq(&self, other: &IntVariant) -> bool {
        match (self, other) {
            (Self::Small(x), Self::Small(y)) => x.eq(y),
            (Self::Small(x), Self::Big(y)) => y.as_ref().eq(&BigInt::from(*x)),
            (Self::Big(x), Self::Small(y)) => x.as_ref().eq(&BigInt::from(*y)),
            (Self::Big(x), Self::Big(y)) => x.eq(y),
        }
    }
}



// Function variant
// ------------------------------------------------------------------------------------------------


#[derive(Clone)]
pub struct Builtin {
    pub func: RFunc,
    pub name: Key,
}

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


#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct Func {
    pub args: ListBinding,
    pub kwargs: Option<MapBinding>,
    pub closure: Map,
    pub expr: Tagged<Expr>,
}


#[derive(Clone)]
pub struct Closure(pub Arc<dyn Fn(&List, Option<&Map>) -> Result<Object, Error> + Send + Sync>);


#[derive(Clone, Serialize, Deserialize)]
pub enum FuncVariant {
    Func(Arc<Func>),
    Builtin(Builtin),

    #[serde(skip)]
    Closure(Closure),
}

impl Debug for FuncVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Func(x) => f.debug_tuple("FuncVariant::Function").field(x).finish(),
            Self::Builtin(_) => f.debug_tuple("FuncVariant::Builtin").finish(),
            Self::Closure(_) => f.debug_tuple("FuncVariant::Closure").finish(),
        }
    }
}

impl From<Func> for FuncVariant {
    fn from(value: Func) -> Self {
        FuncVariant::Func(Arc::new(value))
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
    fn user_eq(&self, other: &FuncVariant) -> bool {
        match (self, other) {
            (FuncVariant::Builtin(x), FuncVariant::Builtin(y)) => x.name == y.name,
            _ => false,
        }
    }

    pub fn call(&self, args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
        match self {
            Self::Builtin(Builtin { func, .. }) => func(args, kwargs),
            Self::Closure(Closure(func)) => func(args, kwargs),
            Self::Func(func) => {
                let Func { args: fargs, kwargs: fkwargs, closure, expr } = func.as_ref();

                let ns = Namespace::Frozen(closure);
                let mut sub = ns.subtend();
                sub.bind_list(&fargs.0, args)?;

                match (fkwargs, kwargs) {
                    (Some(b), Some(k)) => { sub.bind_map(&b.0, k)?; },
                    (Some(b), None) => { sub.bind_map(&b.0, &Map::new())?; },
                    _ => {},
                }

                sub.eval(expr)
            }
        }
    }
}


pub type Key = GlobalSymbol;
pub type List = Vec<Object>;
pub type Map = IndexMap<Key, Object>;
pub type RFunc = fn(&List, Option<&Map>) -> Result<Object, Error>;


const SERIALIZE_VERSION: i32 = 1;


#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Type {
    Integer,
    Float,
    String,
    Boolean,
    List,
    Map,
    Function,
    Null,
}

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


#[derive(Clone, Serialize, Deserialize)]
pub enum ObjectVariant {
    Int(IntVariant),
    Float(f64),
    Str(StrVariant),
    Boolean(bool),
    List(Arc<List>),
    Map(Arc<Map>),
    Func(FuncVariant),
    Null,
}

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

impl Debug for ObjectVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(x) => f.debug_tuple("ObjectVariant::Int").field(x).finish(),
            Self::Float(x) => f.debug_tuple("ObjectVariant::Float").field(x).finish(),
            Self::Str(x) => f.debug_tuple("ObjectVariant::Str").field(x).finish(),
            Self::Boolean(x) => f.debug_tuple("ObjectVariant::Boolean").field(x).finish(),
            Self::List(x) => f.debug_tuple("ObjectVariant::List").field(x.as_ref()).finish(),
            Self::Map(x) => f.debug_tuple("ObjectVariant::Map").field(x.as_ref()).finish(),
            Self::Func(x) => f.debug_tuple("ObjectVariant::Function").field(x).finish(),
            Self::Null => f.debug_tuple("ObjectVariant::Null").finish(),
        }
    }
}

impl ObjectVariant {
    pub fn object(self) -> Object {
        Object(self)
    }

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

    pub fn list<T>(x: T) -> Self where T: ToVec<Object> {
        Self::List(Arc::new(x.to_vec()))
    }

    pub fn map<T>(x: T) -> Self where T: ToMap<Key, Object> {
        Self::Map(Arc::new(x.to_map()))
    }

    pub fn function<T>(x: T) -> Self where FuncVariant: From<T> {
        Self::Func(FuncVariant::from(x))
    }

    pub fn numeric_normalize(self) -> Self {
        if let Self::Int(x) = self {
            Self::Int(x.normalize())
        } else {
            self
        }
    }

    pub fn format(&self) -> Result<String, Error> {
        match self {
            Self::Str(r) => Ok(r.format()),
            Self::Int(r) => Ok(r.to_string()),
            Self::Float(r) => Ok(r.to_string()),
            Self::Boolean(true) => Ok("true".to_string()),
            Self::Boolean(false) => Ok("false".to_string()),
            Self::Null => Ok("null".to_string()),
            _ => Err(Error::new(TypeMismatch::Interpolate(self.type_of()))),
        }
    }

    pub fn truthy(&self) -> bool {
        match self {
            Self::Null => false,
            Self::Boolean(val) => *val,
            Self::Int(r) => r.nonzero(),
            Self::Float(r) => *r != 0.0,
            _ => true,
        }
    }

    pub fn user_eq(&self, other: &Self) -> bool {
        match (self, other) {

            // Equality between disparate types
            (Self::Float(x), Self::Int(y)) => y.eq(x),
            (Self::Int(x), Self::Float(y)) => x.eq(y),

            // Structural equality
            (Self::Int(x), Self::Int(y)) => x.user_eq(y),
            (Self::Float(x), Self::Float(y)) => x.eq(y),
            (Self::Str(x), Self::Str(y)) => x.user_eq(y),
            (Self::Boolean(x), Self::Boolean(y)) => x.eq(y),
            (Self::Null, Self::Null) => true,
            (Self::Func(x), Self::Func(y)) => x.user_eq(y),

            // Composite objects => use user equality
            (Self::List(x), Self::List(y)) => {
                if x.len() != y.len() {
                    return false
                }
                for (xx, yy) in x.iter().zip(y.as_ref()) {
                    if !xx.user_eq(yy) {
                        return false
                    }
                }
                true
            },

            (Self::Map(x), Self::Map(y)) => {
                if x.len() != y.len() {
                    return false
                }
                for (xk, xv) in x.iter() {
                    if let Some(yv) = y.get(xk) {
                        if !xv.user_eq(yv) {
                            return false
                        }
                    } else {
                        return false
                    }
                }
                true
            },

            // Note: functions always compare false
            _ => false,
        }
    }

    pub fn neg(&self) -> Result<Self, Error> {
        match self {
            Self::Int(x) => Ok(Self::Int(x.neg())),
            Self::Float(x) => Ok(Self::Float(-x)),
            _ => Err(Error::new(TypeMismatch::UnOp(self.type_of(), UnOp::ArithmeticalNegate))),
        }
    }

    pub fn add(&self, other: &Self) -> Result<Self, Error> {
        match (&self, &other) {
            (Self::List(x), Self::List(y)) => Ok(Self::list(x.iter().chain(y.iter()).map(Object::clone).collect::<List>())),
            (Self::Str(x), Self::Str(y)) => Ok(Self::Str(x.add(y))),
            _ => self.operate(other, IntVariant::add, |x,y| x + y, BinOp::Add),
        }
    }

    pub fn sub(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, IntVariant::sub, |x,y| x - y, BinOp::Subtract)
    }

    pub fn mul(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, IntVariant::mul, |x,y| x * y, BinOp::Multiply)
    }

    pub fn div(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, IntVariant::div, |x,y| x / y, BinOp::Divide)
    }

    pub fn idiv(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, IntVariant::idiv, |x,y| (x / y).floor() as f64, BinOp::IntegerDivide)
    }

    fn operate<F,G,S,T>(&self, other: &Self, ixi: F, fxf: G, op: BinOp) -> Result<Self, Error>
    where
        F: Fn(&IntVariant, &IntVariant) -> S,
        G: Fn(f64, f64) -> T,
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

    pub fn cmp_bool(&self, other: &Self, ordering: Ordering) -> Option<bool> {
        self.partial_cmp(other).map(|x| x == ordering)
    }

    pub fn index(&self, other: &Object) -> Result<Object, Error> {
        match (self, &other.0) {
            (Self::List(x), Self::Int(y)) => {
                let i: usize = y.try_into().map_err(|_| Error::new(Value::OutOfRange))?;
                if i >= x.len() {
                    Err(Error::new(Value::OutOfRange))
                } else {
                    Ok(x[i].clone())
                }
            }
            (Self::Map(x), Self::Str(y)) => {
                let yy = GlobalSymbol::from(y);
                x.get(&yy).ok_or_else(|| Error::new(Reason::Unassigned(yy))).map(Object::clone)
            }
            _ => Err(Error::new(TypeMismatch::BinOp(self.type_of(), other.type_of(), BinOp::Index))),
        }
    }

    pub fn call(&self, args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
        match self {
            Self::Func(func) => func.call(args, kwargs),
            _ => Err(Error::new(TypeMismatch::Call(self.type_of()))),
        }
    }

    pub fn get_list<'a>(&'a self) -> Option<&'a List> {
        match self {
            Self::List(x) => Some(x.as_ref()),
            _ => None
        }
    }

    pub fn get_map<'a>(&'a self) -> Option<&'a Map> {
        match self {
            Self::Map(x) => Some(x.as_ref()),
            _ => None
        }
    }

    pub fn get_key(&self) -> Option<Key> {
        match self {
            Self::Str(x) => Some(Key::from(x)),
            _ => None,
        }
    }

    pub fn get_str(&self) -> Option<&str> {
        match self {
            Self::Str(x) => Some(x.as_str()),
            _ => None,
        }
    }

    pub fn get_int(&self) -> Option<&IntVariant> {
        match self {
            Self::Int(x) => Some(x),
            _ => None,
        }
    }

    pub fn get_float(&self) -> Option<f64> {
        match self {
            Self::Float(x) => Some(*x),
            _ => None,
        }
    }

    pub fn get_bool(&self) -> Option<bool> {
        match self {
            Self::Boolean(x) => Some(*x),
            _ => None,
        }
    }

    pub fn get_func(&self) -> Option<&FuncVariant> {
        match self {
            Self::Func(x) => Some(x),
            _ => None,
        }
    }

    pub fn get_null(&self) -> Option<()> {
        match self {
            Self::Null => Some(()),
            _ => None,
        }
    }

    pub fn is_null(&self) -> bool {
        match self {
            ObjectVariant::Null => true,
            _ => false,
        }
    }

    pub fn to_f64(&self) -> Option<f64> {
        match self {
            Self::Int(x) => Some(x.to_f64()),
            Self::Float(x) => Some(*x),
            _ => None,
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
                let mut iter = elements.iter().peekable();
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
                let mut iter = elements.iter().peekable();
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

impl TryFrom<ObjectVariant> for JsonValue {
    type Error = Error;

    fn try_from(value: ObjectVariant) -> Result<Self, Self::Error> {
        match value {
            ObjectVariant::Int(x) => i64::try_from(&x).map_err(|_| Error::new(Value::TooLarge)).map(JsonValue::from),
            ObjectVariant::Float(x) => Ok(JsonValue::from(x)),
            ObjectVariant::Str(x) => Ok(JsonValue::from(x.as_str())),
            ObjectVariant::Boolean(x) => Ok(JsonValue::from(x)),
            ObjectVariant::List(x) => {
                let mut val = JsonValue::new_array();
                for element in x.as_ref() {
                    val.push(JsonValue::try_from(element.clone())?).unwrap();
                }
                Ok(val)
            },
            ObjectVariant::Map(x) => {
                let mut val = JsonValue::new_object();
                for (key, element) in x.as_ref() {
                    val[key.as_str()] = JsonValue::try_from(element.clone())?;
                }
                Ok(val)
            },
            ObjectVariant::Null => Ok(JsonValue::Null),
            _ => Err(Error::new(TypeMismatch::Json(value.type_of()))),
        }
    }
}



macro_rules! wrap1 {
    ($name:ident) => {
        pub fn $name(&self) -> Result<Self, Error> {
            self.0.$name().map(Self)
        }
    };
}

macro_rules! wrap2 {
    ($name:ident) => {
        pub fn $name(&self, other: &Self) -> Result<Self, Error> {
            self.0.$name(&other.0).map(Self)
        }
    };
}


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


#[macro_export]
macro_rules! signature {
    ($args:ident = [ $($param:ident : $type:ident),* ] $block:block) => {
        signature!(0 ; $args [ $($param : $type),* ] , $block)
    };

    ($index:expr ; $args:ident [ $param:ident : $type:ident , $($params:ident : $types:ident),+ ] , $block:block) => {
        if let Some($param) = extract!($index, $args, $type) {
            signature!($index + 1 ; $args [ $($params : $types),* ] , $block)
        }
    };

    ($index:expr ; $args:ident [ $param:ident : $type:ident ] , $block:block) => {
        if let Some($param) = extract!($index, $args, $type) {
            signature!($index + 1 ; $args [ ] , $block)
        }
    };

    ($index:expr ; $args:ident [ ] , $block:block) => {
        if $args.len() == $index $block
    };
}

pub use signature;



#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Object(ObjectVariant);

impl Object {
    pub fn str_interned(val: impl AsRef<str>) -> Self {
        Self(ObjectVariant::Str(StrVariant::interned(val)))
    }

    pub fn str_natural(val: impl AsRef<str>) -> Self {
        Self(ObjectVariant::Str(StrVariant::natural(val)))
    }

    pub fn str(val: impl AsRef<str>) -> Self {
        if val.as_ref().len() < 20 {
            Self::str_interned(val)
        } else {
            Self::str_natural(val)
        }
    }

    pub fn key(val: Key) -> Self {
        Self(ObjectVariant::Str(StrVariant::Interned(val)))
    }

    pub fn int<T>(val: T) -> Self
    where
        IntVariant: From<T>
    {
        Self(ObjectVariant::Int(IntVariant::from(val)))
    }

    pub fn bigint(x: impl AsRef<str>) -> Option<Self> {
        BigInt::from_str(x.as_ref()).ok().map(|x| Self(ObjectVariant::from(x)))
    }

    pub fn float(val: f64) -> Self {
        Self(ObjectVariant::Float(val))
    }

    pub fn bool(val: bool) -> Self {
        Self(ObjectVariant::Boolean(val))
    }

    pub fn null() -> Self {
        Self(ObjectVariant::Null)
    }

    pub fn func<T>(val: T) -> Self
    where
        FuncVariant: From<T>
    {
        Self(ObjectVariant::Func(FuncVariant::from(val)))
    }

    pub fn list(x: impl ToVec<Object>) -> Self {
        Self(ObjectVariant::list(x))
    }

    pub fn map<T>(x: T) -> Self where T: ToMap<Key, Object> {
        Self(ObjectVariant::map(x))
    }

    pub fn variant(&self) -> &ObjectVariant {
        &self.0
    }

    pub fn serialize(&self) -> Option<Vec<u8>> {
        let data = (SERIALIZE_VERSION, SystemTime::now(), self);
        encode::to_vec(&data).ok()
    }

    pub fn serialize_write<T: Write + ?Sized>(&self, out: &mut T) -> Result<(), String> {
        let data = (SERIALIZE_VERSION, SystemTime::now(), self);
        encode::write(out, &data).map_err(|x| x.to_string())
    }

    pub fn deserialize(data: &Vec<u8>) -> Option<(Self, SystemTime)> {
        let (version, time, retval) = decode::from_slice::<(i32, SystemTime, Self)>(data.as_slice()).ok()?;
        if version < SERIALIZE_VERSION {
            None
        } else {
            Some((retval, time))
        }
    }

    pub fn deserialize_read<T: Read>(data: T) -> Result<(Self, SystemTime), String> {
        let (version, time, retval) = decode::from_read::<T, (i32, SystemTime, Self)>(data).map_err(|x| x.to_string())?;
        if version < SERIALIZE_VERSION {
            Err("wrong version".to_string())
        } else {
            Ok((retval, time))
        }
    }

    pub fn numeric_normalize(self) -> Self {
        Self(self.0.numeric_normalize())
    }

    wrap1!{neg}
    wrap2!{add}
    wrap2!{sub}
    wrap2!{mul}
    wrap2!{div}
    wrap2!{idiv}
    wrap2!{pow}
}

impl Deref for Object {
    type Target = ObjectVariant;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl FromIterator<Object> for Object {
    fn from_iter<T: IntoIterator<Item = Object>>(iter: T) -> Self {
        Object(ObjectVariant::List(Arc::new(iter.into_iter().collect())))
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
        Self::try_from(value.0)
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


