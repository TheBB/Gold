use std::{rc::Rc, str::FromStr};

use rug::Integer;

use crate::object::*;


pub fn len(args: &List, _: &Map) -> Result<Object, String> {
    match &args[..] {
        [Object::String(x)] => Ok(Object::from(x.chars().count())),
        [Object::List(x)] => Ok(Object::from(x.len())),
        [Object::Map(x)] => Ok(Object::from(x.len())),
        _ => Err("???".to_string()),
    }
}


pub fn range(args: &List, _: &Map) -> Result<Object, String> {
    match &args[..] {
        [Object::Integer(start), Object::Integer(stop)] =>
            Ok(Object::List(Rc::new((*start..*stop).map(Object::from).collect()))),
        [Object::Integer(stop)] =>
            Ok(Object::List(Rc::new((0..*stop).map(Object::from).collect()))),
        _ => Err("???".to_string()),
    }
}


pub fn to_int(args: &List, _: &Map) -> Result<Object, String> {
    match &args[..] {
        [Object::Integer(_)] => Ok(args[0].clone()),
        [Object::BigInteger(_)] => Ok(args[0].clone()),
        [Object::Float(x)] => Ok(Object::Integer(x.round() as i64)),
        [Object::Boolean(x)] => Ok(Object::from(if *x { 1 } else { 0 })),
        [Object::String(x)] =>
            Integer::from_str(x.as_str()).map_err(|_| "???".to_string()).map(Object::from).map(Object::numeric_normalize),
        _ => Err("???".to_string()),
    }
}


pub fn to_float(args: &List, _: &Map) -> Result<Object, String> {
    match &args[..] {
        [Object::Integer(x)] => Ok(Object::from(*x as f64)),
        [Object::BigInteger(x)] => Ok(Object::from(x.to_f64())),
        [Object::Float(_)] => Ok(args[0].clone()),
        [Object::Boolean(x)] => Ok(Object::from(if *x { 1.0 } else { 0.0 })),
        [Object::String(x)] => f64::from_str(x).map_err(|_| "???".to_string()).map(Object::from),
        _ => Err("???".to_string()),
    }
}


pub fn to_bool(args: &List, _: &Map) -> Result<Object, String> {
    match &args[..] {
        [x] => Ok(Object::from(x.truthy())),
        _ => Err("???".to_string()),
    }
}


pub fn to_str(args: &List, _: &Map) -> Result<Object, String> {
    match &args[..] {
        [Object::String(_)] => Ok(args[0].clone()),
        _ => Ok(Object::from(args[0].to_string().as_str())),
    }
}
