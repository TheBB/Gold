use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::Debug;
use std::io::{Read, Write};
use std::str::FromStr;
use std::sync::Arc;
use std::time::SystemTime;

use num_bigint::BigInt;
use num_traits::ToPrimitive;
use json::JsonValue;
use rmp_serde::{decode, encode};
use serde::de::Visitor;
use serde::{Serialize, Serializer, Deserialize, Deserializer};

use crate::builtins::BUILTINS;
use crate::traits::{ToVec, ToMap};

use super::util;
use super::ast::{Binding, Expr};
use super::traits::{Splattable, Splat};


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


pub type Key = Arc<String>;
pub type List = Vec<Object>;
pub type Map = HashMap<Key, Object>;
pub type RFunc = fn(&List, &Map) -> Result<Object, String>;


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
        BUILTINS.get(v).ok_or(E::custom("unknown builtin name")).map(
            |x| Builtin { name: Key::new(v.to_string()), func: *x }
        )
    }
}

impl<'a> Deserialize<'a> for Builtin {
    fn deserialize<D: Deserializer<'a>>(deserializer: D) -> Result<Self, D::Error> where {
        deserializer.deserialize_str(BuiltinVisitor)
    }
}


#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub struct Function {
    pub args: Binding,
    pub kwargs: Binding,
    pub closure: Map,
    pub expr: Expr,
}


#[derive(Clone, Serialize, Deserialize)]
pub enum Object {
    Integer(i64),
    BigInteger(Arc<BigInt>),
    Float(f64),
    String(Key),
    Boolean(bool),
    List(Arc<List>),
    Map(Arc<Map>),
    Function(Arc<Function>),
    Builtin(Builtin),
    Null,
}

impl Splattable<Object> for Object {
    fn splat(&self) -> Splat<Object> { Splat::<Object> { object: self.clone() } }
}

impl PartialEq<Object> for Object {
    fn eq(&self, other: &Object) -> bool {
        match (self, other) {
            (Self::Integer(x), Self::Integer(y)) => x.eq(y),
            (Self::BigInteger(x), Self::BigInteger(y)) => x.eq(y),
            (Self::Float(x), Self::Float(y)) => x.eq(y),
            (Self::String(x), Self::String(y)) => x.eq(y),
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
            (Object::String(x), Object::String(y)) => x.partial_cmp(y),
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
            Self::String(x) => f.debug_tuple("Object::String").field(x).finish(),
            Self::Boolean(x) => f.debug_tuple("Object::Boolean").field(x).finish(),
            Self::List(x) => f.debug_tuple("Object::List").field(x.as_ref()).finish(),
            Self::Map(x) => f.debug_tuple("Object::Map").field(x.as_ref()).finish(),
            Self::Function(x) => f.debug_tuple("Object::Function").field(x.as_ref()).finish(),
            Self::Builtin(_) => f.debug_tuple("Object::Builtin").finish(),
            Self::Null => f.debug_tuple("Object::Null").finish(),
        }
    }
}

impl Object {
    pub fn string<T: ToString>(x: T) -> Object {
        Object::String(Arc::new(x.to_string()))
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
            Object::String(r) => Ok(r.to_string()),
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
            (Object::String(x), Object::String(y)) => x.eq(y),
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
    fn from(x: &str) -> Object { Object::String(Key::new(x.to_string())) }
}

impl From<bool> for Object {
    fn from(x: bool) -> Object { Object::Boolean(x) }
}

impl TryInto<f64> for Object {
    type Error = ();
    fn try_into(self) -> Result<f64, Self::Error> {
        match self {
            Object::Integer(x) => Ok(x as f64),
            Object::BigInteger(x) => Ok(util::big_to_f64(x.as_ref())),
            Object::Float(x) => Ok(x),
            _ => Err(()),
        }
    }
}

impl ToString for Object {
    fn to_string(&self) -> String {
        match self {
            Object::String(r) => format!("\"{}\"", escape(r)),
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
                    retval += k;
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
            Object::String(x) => Ok(JsonValue::from(x.as_str())),
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
                    val[key.as_ref()] = JsonValue::try_from(element.clone())?;
                }
                Ok(val)
            },
            Object::Null => Ok(JsonValue::Null),
            _ => Err("uncovertible type".to_string()),
        }
    }
}
