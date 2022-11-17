use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Debug;
use std::io::{Read, Write};
use std::str::FromStr;
use std::sync::Arc;
use std::time::SystemTime;

use symbol_table::GlobalSymbol;
use num_bigint::BigInt;
use num_traits::{ToPrimitive, checked_pow};
use json::JsonValue;
use rmp_serde::{decode, encode};
use serde::de::Visitor;
use serde::{Serialize, Serializer, Deserialize, Deserializer};

use crate::builtins::BUILTINS;
use crate::traits::{ToVec, ToMap};

use crate::ast::{ListBinding, MapBinding, Expr};
use crate::error::Tagged;
use crate::eval::Namespace;
use crate::util;


fn escape(s: &str) -> String {
    let mut r = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => { r.push_str("\\\""); }
            '\\' => { r.push_str("\\\\"); }
            _ => { r.push(c); }
        }
    }
    r
}


struct Arith<F,G,H,X,Y,Z>
where
    F: Fn(i64, i64) -> Option<X>,
    G: Fn(&BigInt, &BigInt) -> Y,
    H: Fn(f64, f64) -> Z,
{
    ixi: F,
    bxb: G,
    fxf: H,
}


fn arithmetic_operate<F,G,H,X,Y,Z>(ops: Arith<F,G,H,X,Y,Z>, x: &Object, y: &Object) -> Result<Object, String>
where
    F: Fn(i64, i64) -> Option<X>,
    G: Fn(&BigInt, &BigInt) -> Y,
    H: Fn(f64, f64) -> Z,
    Object: From<X>,
    Object: From<Y>,
    Object: From<Z>,
{
    let Arith { ixi, bxb, fxf } = ops;

    match (x, y) {
        (Object::Integer(xx), Object::Integer(yy)) => Ok(
            ixi(*xx, *yy).map(Object::from).unwrap_or_else(
                || Object::from(bxb(&BigInt::from(*xx), &BigInt::from(*yy))).numeric_normalize()
            )
        ),

        (Object::Integer(xx), Object::BigInteger(yy)) => Ok(Object::from(bxb(&BigInt::from(*xx), yy.as_ref())).numeric_normalize()),
        (Object::BigInteger(xx), Object::Integer(yy)) => Ok(Object::from(bxb(xx.as_ref(), &BigInt::from(*yy))).numeric_normalize()),
        (Object::BigInteger(xx), Object::BigInteger(yy)) => Ok(Object::from(bxb(xx.as_ref(), yy.as_ref())).numeric_normalize()),

        (Object::Float(xx), Object::Float(yy)) => Ok(Object::from(fxf(*xx, *yy))),
        (Object::Integer(xx), Object::Float(yy)) => Ok(Object::from(fxf(*xx as f64, *yy))),
        (Object::Float(xx), Object::Integer(yy)) => Ok(Object::from(fxf(*xx, *yy as f64))),

        (Object::Float(xx), Object::BigInteger(yy)) => Ok(Object::from(fxf(*xx, util::big_to_f64(yy.as_ref())))),
        (Object::BigInteger(xx), Object::Float(yy)) => Ok(Object::from(fxf(util::big_to_f64(xx.as_ref()), *yy))),

        _ => Err("unsupported types for arithmetic".to_string()),
    }
}


pub type Key = GlobalSymbol;
pub type List = Vec<Object>;
pub type Map = HashMap<Key, Object>;
pub type RFunc = fn(&List, Option<&Map>) -> Result<Object, String>;


const SERIALIZE_VERSION: i32 = 1;


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
pub struct Function {
    pub args: ListBinding,
    pub kwargs: Option<MapBinding>,
    pub closure: Map,
    pub expr: Tagged<Expr>,
}


#[derive(Clone)]
pub struct Closure(pub Arc<dyn Fn(&List, Option<&Map>) -> Result<Object, String> + Send + Sync>);


#[derive(Clone, Serialize, Deserialize)]
pub enum Object {
    Integer(i64),
    BigInteger(Arc<BigInt>),
    Float(f64),

    IntString(GlobalSymbol),
    NatString(Arc<String>),

    Boolean(bool),
    List(Arc<List>),
    Map(Arc<Map>),
    Function(Arc<Function>),
    Builtin(Builtin),
    Null,

    #[serde(skip)]
    Closure(Closure),
}

impl PartialEq<Object> for Object {
    fn eq(&self, other: &Object) -> bool {
        match (self, other) {
            (Self::Integer(x), Self::Integer(y)) => x.eq(y),
            (Self::BigInteger(x), Self::BigInteger(y)) => x.eq(y),
            (Self::Float(x), Self::Float(y)) => x.eq(y),
            (Self::IntString(x), Self::IntString(y)) => x.eq(y),
            (Self::NatString(x), Self::NatString(y)) => x.eq(y),
            (Self::Boolean(x), Self::Boolean(y)) => x.eq(y),
            (Self::List(x), Self::List(y)) => x.eq(y),
            (Self::Map(x), Self::Map(y)) => x.eq(y),
            (Self::Null, Self::Null) => true,
            _ => false,
        }
    }
}

impl PartialOrd<Object> for Object {
    fn partial_cmp(&self, other: &Object) -> Option<Ordering> {
        match (self, other) {
            (Object::Integer(x), Object::Integer(y)) => x.partial_cmp(y),
            (Object::Integer(x), Object::BigInteger(y)) => BigInt::from(*x).partial_cmp(y),
            (Object::Integer(x), Object::Float(y)) => (*x as f64).partial_cmp(y),
            (Object::BigInteger(x), Object::Integer(y)) => x.as_ref().partial_cmp(&BigInt::from(*y)),
            (Object::BigInteger(x), Object::BigInteger(y)) => x.as_ref().partial_cmp(y.as_ref()),
            (Object::BigInteger(x), Object::Float(y)) => {
                let (lo, hi) = util::f64_to_bigs(*y);
                if x.as_ref() < &lo || x.as_ref() == &lo && lo != hi {
                    Some(Ordering::Less)
                } else if x.as_ref() > &hi || x.as_ref() == &hi && lo != hi {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Equal)
                }
            },
            (Object::Float(x), Object::Integer(y)) => x.partial_cmp(&(*y as f64)),
            (Object::Float(_), Object::BigInteger(_)) => other.partial_cmp(self).map(Ordering::reverse),
            (Object::Float(x), Object::Float(y)) => x.partial_cmp(y),
            (Object::IntString(x), Object::IntString(y)) => x.as_str().partial_cmp(y.as_str()),
            (Object::NatString(x), Object::IntString(y)) => x.as_str().partial_cmp(y.as_str()),
            (Object::IntString(x), Object::NatString(y)) => x.as_str().partial_cmp(y.as_str()),
            (Object::NatString(x), Object::NatString(y)) => x.as_str().partial_cmp(y.as_str()),
            _ => None,
        }
    }
}

impl Debug for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(x) => f.debug_tuple("Object::Integer").field(x).finish(),
            Self::BigInteger(x) => f.debug_tuple("Object::BigInteger").field(x).finish(),
            Self::Float(x) => f.debug_tuple("Object::Float").field(x).finish(),
            Self::IntString(x) => f.debug_tuple("Object::IntString").field(x).finish(),
            Self::NatString(x) => f.debug_tuple("Object::NatString").field(x).finish(),
            Self::Boolean(x) => f.debug_tuple("Object::Boolean").field(x).finish(),
            Self::List(x) => f.debug_tuple("Object::List").field(x.as_ref()).finish(),
            Self::Map(x) => f.debug_tuple("Object::Map").field(x.as_ref()).finish(),
            Self::Function(x) => f.debug_tuple("Object::Function").field(x.as_ref()).finish(),
            Self::Builtin(_) => f.debug_tuple("Object::Builtin").finish(),
            Self::Null => f.debug_tuple("Object::Null").finish(),
            Self::Closure(_) => f.debug_tuple("Object::Closure").finish(),
        }
    }
}

impl Object {
    pub fn int_string<T: AsRef<str>>(x: T) -> Object {
        Object::IntString(GlobalSymbol::new(x))
    }

    pub fn nat_string<T: AsRef<str>>(x: T) -> Object {
        Object::NatString(Arc::new(x.as_ref().to_string()))
    }

    pub fn bigint(x: &str) -> Option<Object> {
        BigInt::from_str(x).ok().map(Object::from)
    }

    pub fn literal(&self) -> Expr {
        Expr::Literal(self.clone())
    }

    pub fn list<T>(x: T) -> Object where T: ToVec<Object> {
        Object::List(Arc::new(x.to_vec()))
    }

    pub fn map<T>(x: T) -> Object where T: ToMap<Key, Object> {
        Object::Map(Arc::new(x.to_map()))
    }

    pub fn format(&self) -> Result<String, String> {
        match self {
            Object::IntString(r) => Ok(r.to_string()),
            Object::Integer(r) => Ok(r.to_string()),
            Object::BigInteger(r) => Ok(r.to_string()),
            Object::Float(r) => Ok(r.to_string()),
            Object::Boolean(true) => Ok("true".to_string()),
            Object::Boolean(false) => Ok("false".to_string()),
            Object::Null => Ok("null".to_string()),
            _ => Err("wrong type".to_string()),
        }
    }

    pub fn truthy(&self) -> bool {
        match self {
            Object::Null => false,
            Object::Boolean(val) => *val,
            Object::Integer(r) => *r != 0,
            Object::Float(r) => *r != 0.0,
            _ => true,
        }
    }

    pub fn numeric_normalize(self) -> Object {
        if let Object::BigInteger(x) = &self {
            x.to_i64().map(Object::from).unwrap_or(self)
        } else {
            self
        }
    }

    pub fn user_eq(&self, other: &Object) -> bool {
        match (self, other) {

            // Equality between disparate types
            (Object::Integer(x), Object::BigInteger(y)) => y.as_ref().eq(&BigInt::from(*x)),
            (Object::BigInteger(x), Object::Integer(y)) => x.as_ref().eq(&BigInt::from(*y)),
            (Object::Float(x), Object::Integer(y)) => x.eq(&(*y as f64)),
            (Object::Integer(x), Object::Float(y)) => y.eq(&(*x as f64)),
            (Object::Float(x), Object::BigInteger(y)) => {
                let (lo, hi) = util::f64_to_bigs(*x);
                lo == hi && &hi == y.as_ref()
            },
            (Object::BigInteger(x), Object::Float(y)) => {
                let (lo, hi) = util::f64_to_bigs(*y);
                lo == hi && &hi == x.as_ref()
            },

            // Structural equality
            (Object::Integer(x), Object::Integer(y)) => x.eq(y),
            (Object::Float(x), Object::Float(y)) => x.eq(y),
            (Object::IntString(x), Object::IntString(y)) => x.eq(y),
            (Object::Boolean(x), Object::Boolean(y)) => x.eq(y),
            (Object::Null, Object::Null) => true,
            (Object::Builtin(x), Object::Builtin(y)) => x.name == y.name,

            // Composite objects => use user equality
            (Object::List(x), Object::List(y)) => {
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

            (Object::Map(x), Object::Map(y)) => {
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

    pub fn serialize(&self) -> Option<Vec<u8>> {
        let data = (SERIALIZE_VERSION, SystemTime::now(), self);
        encode::to_vec(&data).ok()
    }

    pub fn serialize_write<T: Write + ?Sized>(&self, out: &mut T) -> Result<(), String> {
        let data = (SERIALIZE_VERSION, SystemTime::now(), self);
        encode::write(out, &data).map_err(|x| x.to_string())
    }

    pub fn deserialize(data: &Vec<u8>) -> Option<(Object, SystemTime)> {
        let (version, time, retval) = decode::from_slice::<(i32, SystemTime, Object)>(data.as_slice()).ok()?;
        if version < SERIALIZE_VERSION {
            None
        } else {
            Some((retval, time))
        }
    }

    pub fn deserialize_read<T: Read>(data: T) -> Result<(Object, SystemTime), String> {
        let (version, time, retval) = decode::from_read::<T, (i32, SystemTime, Object)>(data).map_err(|x| x.to_string())?;
        if version < SERIALIZE_VERSION {
            Err("wrong version".to_string())
        } else {
            Ok((retval, time))
        }
    }

    pub fn neg(&self) -> Result<Object, String> {
        match self {
            Object::Integer(x) => {
                if let Some(y) = x.checked_neg() {
                    Ok(Object::from(y))
                } else {
                    Object::from(BigInt::from(*x)).neg()
                }
            },
            Object::BigInteger(x) => Ok(Object::from(-x.as_ref()).numeric_normalize()),
            Object::Float(x) => Ok(Object::from(-x)),
            _ => Err("type mismatch".to_string()),
        }
    }

    pub fn add(&self, other: &Object) -> Result<Object, String> {
        match (&self, &other) {
            (Object::List(x), Object::List(y)) => Ok(Object::from(x.iter().chain(y.iter()).map(Object::clone).collect::<List>())),
            (Object::IntString(x), Object::IntString(y)) => Ok(Object::nat_string(format!("{}{}", x.as_str(), y.as_str()))),
            (Object::NatString(x), Object::IntString(y)) => Ok(Object::nat_string(format!("{}{}", x.as_str(), y.as_str()))),
            (Object::IntString(x), Object::NatString(y)) => Ok(Object::nat_string(format!("{}{}", x.as_str(), y.as_str()))),
            (Object::NatString(x), Object::NatString(y)) => Ok(Object::nat_string(format!("{}{}", x.as_str(), y.as_str()))),
            _ => arithmetic_operate(Arith {
                ixi: i64::checked_add,
                bxb: |x,y| x + y,
                fxf: |x,y| x + y,
            }, self, other),
        }
    }

    pub fn sub(&self, other: &Object) -> Result<Object, String> {
        arithmetic_operate(Arith {
            ixi: i64::checked_sub,
            bxb: |x,y| x - y,
            fxf: |x,y| x - y,
        }, self, other)
    }

    pub fn mul(&self, other: &Object) -> Result<Object, String> {
        arithmetic_operate(Arith {
            ixi: i64::checked_mul,
            bxb: |x,y| x * y,
            fxf: |x,y| x * y,
        }, self, other)
    }

    pub fn div(&self, other: &Object) -> Result<Object, String> {
        arithmetic_operate(Arith {
            ixi: |x,y| Some((x as f64) / (y as f64)),
            bxb: |x,y| util::big_to_f64(x) / util::big_to_f64(y),
            fxf: |x,y| x / y,
        }, self, other)
    }

    pub fn idiv(self, other: Object) -> Result<Object, String> {
        arithmetic_operate(Arith {
            ixi: i64::checked_div,
            bxb: |x,y| x / y,
            fxf: |x,y| (x / y).floor() as f64,
        }, &self, &other)
    }

    pub fn pow(&self, other: &Object) -> Result<Object, String> {
        match (self, other) {
            (Object::Integer(x), Object::Integer(y)) if *y >= 0 => {
                let yy: u32 = (*y).try_into().or_else(|_| Err("unable to convert exponent"))?;
                Ok(checked_pow(*x, yy as usize).map(Object::from).unwrap_or_else(
                    || Object::from(BigInt::from(*x).pow(yy))
                ))
            },

            (Object::BigInteger(x), Object::Integer(y)) if *y >= 0 => {
                let yy: u32 = (*y).try_into().or_else(|_| Err("unable to convert exponent"))?;
                Ok(Object::from(x.as_ref().pow(yy)))
            },

            _ => {
                let xx: f64 = self.to_f64().ok_or_else(|| "wrong type for power".to_string())?;
                let yy: f64 = other.to_f64().ok_or_else(|| "wrong type for power".to_string())?;
                Ok(Object::from(xx.powf(yy)))
            },
        }
    }

    pub fn cmp_bool(&self, other: &Object, ordering: Ordering) -> Result<bool, String> {
        self.partial_cmp(other).map(|x| x == ordering).ok_or_else(|| "err".to_string())
    }

    pub fn index(&self, other: &Object) -> Result<Object, String> {
        match (self, other) {
            (Object::List(x), Object::Integer(y)) => Ok(x[*y as usize].clone()),
            (Object::Map(x), Object::IntString(y)) => x.get(y).ok_or_else(|| "unknown key".to_string()).map(Object::clone),
            (Object::Map(x), Object::NatString(y)) => x.get(&GlobalSymbol::new(y.as_ref())).ok_or_else(|| "unknown key".to_string()).map(Object::clone),
            _ => Err("unsupported types for indexing".to_string()),
        }
    }

    pub fn call(&self, args: &List, kwargs: Option<&Map>) -> Result<Object, String> {
        match self {
            Object::Function(func) => {
                let Function { args: fargs, kwargs: fkwargs, closure, expr } = func.as_ref();

                let ns = Namespace::Frozen(closure);
                let mut sub = ns.subtend();
                sub.bind_list(&fargs.0, args)?;

                match (fkwargs, kwargs) {
                    (Some(b), Some(k)) => { sub.bind_map(&b.0, k)?; },
                    (Some(b), None) => { sub.bind_map(&b.0, &Map::new())?; },
                    _ => {},
                }

                sub.eval(expr)
            },
            Object::Builtin(Builtin { func, .. }) => {
                func(args, kwargs)
            },
            Object::Closure(Closure(func)) => {
                func(args, kwargs)
            }
            _ => Err("calling a non-function".to_string()),
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

    pub fn to_f64(&self) -> Option<f64> {
        match self {
            Object::Integer(x) => Some(*x as f64),
            Object::BigInteger(x) => Some(util::big_to_f64(x.as_ref())),
            Object::Float(x) => Some(*x),
            _ => None,
        }
    }
}

impl From<&i64> for Object {
    fn from(x: &i64) -> Object { Object::Integer(*x) }
}

impl From<i64> for Object {
    fn from(x: i64) -> Object { Object::Integer(x) }
}

impl From<i32> for Object {
    fn from(x: i32) -> Object { Object::Integer(x as i64) }
}

impl From<f64> for Object {
    fn from(x: f64) -> Object { Object::Float(x) }
}

impl From<usize> for Object {
    fn from(value: usize) -> Object {
        i64::try_from(value).map(Object::from).unwrap_or_else(
            |_| Object::from(BigInt::from(value))
        )
    }
}

impl From<BigInt> for Object {
    fn from(x: BigInt) -> Object { Object::BigInteger(Arc::new(x)) }
}

impl From<&str> for Object {
    fn from(x: &str) -> Object {
        if x.len() < 20 {
            Object::int_string(x)
        } else {
            Object::nat_string(x)
        }
    }
}

impl From<Key> for Object where {
    fn from(value: Key) -> Self {
        Object::IntString(value)
    }
}

impl From<bool> for Object {
    fn from(x: bool) -> Object { Object::Boolean(x) }
}

impl From<List> for Object {
    fn from(value: List) -> Self {
        Object::List(Arc::new(value))
    }
}

impl From<Map> for Object {
    fn from(value: Map) -> Self {
        Object::Map(Arc::new(value))
    }
}

impl From<Function> for Object {
    fn from(value: Function) -> Self {
        Object::Function(Arc::new(value))
    }
}

impl From<Builtin> for Object {
    fn from(value: Builtin) -> Self {
        Object::Builtin(value)
    }
}

impl ToString for Object {
    fn to_string(&self) -> String {
        match self {
            Object::IntString(r) => format!("\"{}\"", escape(r.as_str())),
            Object::Integer(r) => r.to_string(),
            Object::BigInteger(r) => r.to_string(),
            Object::Float(r) => r.to_string(),
            Object::Boolean(true) => "true".to_string(),
            Object::Boolean(false) => "false".to_string(),
            Object::Null => "null".to_string(),

            Object::List(elements) => {
                let mut retval = "[".to_string();
                let mut iter = elements.iter().peekable();
                while let Some(element) = iter.next() {
                    retval += &element.to_string();
                    if iter.peek().is_some() {
                        retval += ", ";
                    }
                }
                retval += "]";
                retval
            }

            Object::Map(elements) => {
                let mut retval = "{".to_string();
                let mut iter = elements.iter().peekable();
                while let Some((k, v)) = iter.next() {
                    retval += k.as_str();
                    retval += ": ";
                    retval += &v.to_string();
                    if iter.peek().is_some() {
                        retval += ", ";
                    }
                }
                retval += "}";
                retval
            }

            _ => "?".to_string(),
        }
    }
}

impl TryFrom<Object> for JsonValue {
    type Error = String;

    fn try_from(value: Object) -> Result<Self, Self::Error> {
        match value {
            Object::Integer(x) => Ok(JsonValue::from(x)),
            Object::BigInteger(_) => Err("too big number".to_string()),
            Object::Float(x) => Ok(JsonValue::from(x)),
            Object::IntString(x) => Ok(JsonValue::from(x.as_str())),
            Object::Boolean(x) => Ok(JsonValue::from(x)),
            Object::List(x) => {
                let mut val = JsonValue::new_array();
                for element in x.as_ref() {
                    val.push(JsonValue::try_from(element.clone())?).map_err(|x| x.to_string())?;
                }
                Ok(val)
            },
            Object::Map(x) => {
                let mut val = JsonValue::new_object();
                for (key, element) in x.as_ref() {
                    val[key.as_str()] = JsonValue::try_from(element.clone())?;
                }
                Ok(val)
            },
            Object::Null => Ok(JsonValue::Null),
            _ => Err("uncovertible type".to_string()),
        }
    }
}
