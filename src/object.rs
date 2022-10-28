use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

use rug::Integer;

use super::ast::{Binding, AstNode};
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


pub type Key = Rc<String>;
pub type List = Vec<Object>;
pub type Map = HashMap<Key, Object>;


#[derive(Debug, PartialEq)]
pub struct Function {
    pub args: Binding,
    pub kwargs: Binding,
    pub closure: Map,
    pub expr: AstNode,
}


#[derive(Debug, Clone, PartialEq)]
pub enum Object {
    Integer(i64),
    BigInteger(Rc<Integer>),
    Float(f64),
    String(Key),
    Boolean(bool),
    List(Rc<List>),
    Map(Rc<Map>),
    Function(Rc<Function>),
    Null,
}

impl Splattable<Object> for Object {
    fn splat(&self) -> Splat<Object> { Splat::<Object> { object: self.clone() } }
}

impl Object {
    pub fn string<T: ToString>(x: T) -> Object { Object::String(Rc::new(x.to_string())) }

    pub fn literal(&self) -> AstNode { AstNode::Literal(self.clone()) }

    pub fn fmt(&self) -> Result<String, String> {
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
}

impl PartialOrd<Object> for Object {
    fn partial_cmp(&self, other: &Object) -> Option<Ordering> {
        match (self, other) {
            (Object::Integer(x), Object::Integer(y)) => x.partial_cmp(y),
            (Object::Integer(x), Object::BigInteger(y)) => x.partial_cmp(y.as_ref()),
            (Object::Integer(x), Object::Float(y)) => (*x as f64).partial_cmp(y),
            (Object::BigInteger(x), Object::Integer(y)) => x.as_ref().partial_cmp(y),
            (Object::BigInteger(x), Object::BigInteger(y)) => x.as_ref().partial_cmp(y.as_ref()),
            (Object::BigInteger(x), Object::Float(y)) => x.as_ref().partial_cmp(y),
            (Object::Float(x), Object::Integer(y)) => x.partial_cmp(&(*y as f64)),
            (Object::Float(x), Object::BigInteger(y)) => x.partial_cmp(y.as_ref()),
            (Object::Float(x), Object::Float(y)) => x.partial_cmp(y),
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

impl From<f64> for Object {
    fn from(x: f64) -> Object { Object::Float(x) }
}

impl From<Integer> for Object {
    fn from(x: Integer) -> Object { Object::BigInteger(Rc::new(x)) }
}

impl From<&str> for Object {
    fn from(x: &str) -> Object { Object::String(Rc::new(x.to_string())) }
}

impl From<bool> for Object {
    fn from(x: bool) -> Object { Object::Boolean(x) }
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
