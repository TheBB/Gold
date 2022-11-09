use std::str::FromStr;
// use std::sync::Arc;

use num_bigint::BigInt;

use phf::phf_map;

use crate::{object::*, util};


pub static BUILTINS: phf::Map<&'static str, RFunc> = phf_map! {
    "len" => len,
    "range" => range,
    "int" => to_int,
    "float" => to_float,
    "bool" => to_bool,
    "str" => to_str,
};


pub fn len(args: &List, _: &Map) -> Result<Object, String> {
    match &args[..] {
        [Object::String(x)] => Ok(Object::from(x.chars().count() as usize)),
        [Object::List(x)] => Ok(Object::from(x.len() as usize)),
        [Object::Map(x)] => Ok(Object::from(x.len() as usize)),
        _ => Err("???".to_string()),
    }
}


pub fn range(args: &List, _: &Map) -> Result<Object, String> {
    match &args[..] {
        [Object::Integer(start), Object::Integer(stop)] =>
            Ok(Object::from((*start..*stop).map(Object::from).collect::<List>())),
        [Object::Integer(stop)] =>
            Ok(Object::from((0..*stop).map(Object::from).collect::<List>())),
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
            BigInt::from_str(x.as_str()).map_err(|_| "???".to_string()).map(Object::from).map(Object::numeric_normalize),
        _ => Err("???".to_string()),
    }
}


pub fn to_float(args: &List, _: &Map) -> Result<Object, String> {
    match &args[..] {
        [Object::Integer(x)] => Ok(Object::from(*x as f64)),
        [Object::BigInteger(x)] => Ok(Object::from(util::big_to_f64(x))),
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
