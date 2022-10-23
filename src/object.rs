use std::collections::HashMap;
use std::rc::Rc;

use ibig::IBig;

use super::ast::{Binding, AstNode};
use super::traits::{Boxable, Splattable, Splat};


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


#[derive(Debug, Clone, PartialEq)]
pub enum Object {
    Integer(i64),
    BigInteger(IBig),
    Float(f64),
    String(Rc<String>),
    Boolean(bool),
    List(Rc<Vec<Object>>),
    Map(Rc<HashMap<Rc<String>, Object>>),
    Function(Binding, Binding, Rc<AstNode>),
    Null,
}

impl Boxable<Object> for Object {
    fn to_box(self) -> Box<Object> { Box::new(self) }
}

impl Splattable<Object> for Object {
    fn splat(self) -> Splat<Object> { Splat::<Object> { object: self } }
}

impl Object {
    pub fn string<T: ToString>(x: T) -> Object { Object::String(Rc::new(x.to_string())) }
    pub fn literal(self) -> AstNode { AstNode::Literal(self) }

    pub fn fmt(self) -> Result<String, String> {
        match self {
            Object::String(r) => Ok((*r).clone()),
            Object::Integer(r) => Ok(r.to_string()),
            Object::BigInteger(r) => Ok(r.to_string()),
            Object::Float(r) => Ok(r.to_string()),
            Object::Boolean(true) => Ok("true".to_string()),
            Object::Boolean(false) => Ok("false".to_string()),
            Object::Null => Ok("null".to_string()),
            _ => Err("wrong type".to_string()),
        }
    }

    pub fn truthy(self) -> bool {
        match self {
            Object::Null => false,
            Object::Boolean(val) => val,
            _ => true,
        }
    }

    pub fn numeric_normalize(self) -> Object {
        if let Object::BigInteger(x) = &self {
            i64::try_from(x).map(Object::Integer).unwrap_or(self)
        } else {
            self
        }
    }
}

impl From<&i64> for Object {
    fn from(x: &i64) -> Object { Object::Integer(*x) }
}

impl From<i64> for Object {
    fn from(x: i64) -> Object { Object::Integer(x) }
}

impl From<f64> for Object {
    fn from(x: f64) -> Object { Object::Float(x) }
}

impl From<IBig> for Object {
    fn from(x: IBig) -> Object { Object::BigInteger(x) }
}

impl TryInto<f64> for Object {
    type Error = ();
    fn try_into(self) -> Result<f64, Self::Error> {
        match self {
            Object::Integer(x) => Ok(x as f64),
            Object::Float(x) => Ok(x),
            Object::BigInteger(x) => Ok(x.to_f64()),
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
                "[".to_string() + &elements.iter().map(Object::to_string).collect::<Vec<String>>().join(", ") + "]"
            }
            _ => "?".to_string(),
        }
    }
}

pub trait ToObject {
    fn to_object(self) -> Object;
}

impl ToObject for &str {
    fn to_object(self) -> Object { Object::String(Rc::new(self.to_string())) }
}

impl ToObject for String {
    fn to_object(self) -> Object { Object::String(Rc::new(self)) }
}

impl ToObject for i32 {
    fn to_object(self) -> Object { Object::Integer(self as i64) }
}

impl ToObject for i64 {
    fn to_object(self) -> Object { Object::Integer(self) }
}

impl ToObject for f64 {
    fn to_object(self) -> Object { Object::Float(self) }
}

impl ToObject for bool {
    fn to_object(self) -> Object { Object::Boolean(self) }
}

impl ToObject for Object {
    fn to_object(self) -> Object { self }
}
