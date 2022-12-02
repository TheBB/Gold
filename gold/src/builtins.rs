use std::str::FromStr;
use std::collections::HashMap;

use num_bigint::BigInt;

use crate::error::Value;
use crate::object::*;
use crate::util;
use crate::error::{Error, TypeMismatch};


macro_rules! builtin {
    ($m: ident, $e: ident) => {
        $m.insert(
            stringify!($e),
            Builtin {
                func: $e,
                name: Key::new(stringify!($e).to_string()),
            },
        )
    };
}


lazy_static! {
    pub static ref BUILTINS: HashMap<&'static str, Builtin> = {
        let mut m = HashMap::new();
        builtin!(m, len);
        builtin!(m, range);
        builtin!(m, int);
        builtin!(m, float);
        builtin!(m, bool);
        builtin!(m, str);
        m
    };
}


pub fn len(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::IntString(x)] => Ok(Object::from(x.as_str().chars().count() as usize)),
        [Object::NatString(x)] => Ok(Object::from(x.as_str().chars().count() as usize)),
        [Object::List(x)] => Ok(Object::from(x.len() as usize)),
        [Object::Map(x)] => Ok(Object::from(x.len() as usize)),
        [obj] => Err(Error::new(TypeMismatch::ExpectedArg(
            0,
            vec![Type::String, Type::List, Type::Map],
            obj.type_of(),
        ))),
        args => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn range(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Integer(start), Object::Integer(stop)] => Ok(Object::from((*start..*stop).map(Object::from).collect::<List>())),
        [Object::Integer(_), y] => Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::Integer], y.type_of()))),
        [x, Object::Integer(_)] => Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Integer], x.type_of()))),
        [Object::Integer(stop)] => Ok(Object::from((0..*stop).map(Object::from).collect::<List>())),
        [x] => Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Integer], x.type_of()))),
        args => Err(Error::new(TypeMismatch::ArgCount(1, 2, args.len()))),
    }
}


pub fn int(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Integer(_)] => Ok(args[0].clone()),
        [Object::BigInteger(_)] => Ok(args[0].clone()),
        [Object::Float(x)] => Ok(Object::Integer(x.round() as i64)),
        [Object::Boolean(x)] => Ok(Object::from(if *x { 1 } else { 0 })),
        [Object::IntString(x)] =>
            BigInt::from_str(x.as_str()).map_err(|_| Error::new(Value::Convert(Type::Integer))).map(Object::from).map(Object::numeric_normalize),
        [Object::NatString(x)] =>
            BigInt::from_str(x.as_str()).map_err(|_| Error::new(Value::Convert(Type::Integer))).map(Object::from).map(Object::numeric_normalize),
        [x] => Err(Error::new(TypeMismatch::ExpectedArg(
            0,
            vec![Type::Integer, Type::Float, Type::Boolean, Type::String],
            x.type_of(),
        ))),
        args => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn float(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Integer(x)] => Ok(Object::from(*x as f64)),
        [Object::BigInteger(x)] => Ok(Object::from(util::big_to_f64(x))),
        [Object::Float(_)] => Ok(args[0].clone()),
        [Object::Boolean(x)] => Ok(Object::from(if *x { 1.0 } else { 0.0 })),
        [Object::IntString(x)] => f64::from_str(x.as_str()).map_err(|_| Error::new(Value::Convert(Type::Float))).map(Object::from),
        [Object::NatString(x)] => f64::from_str(x.as_str()).map_err(|_| Error::new(Value::Convert(Type::Float))).map(Object::from),
        [x] => Err(Error::new(TypeMismatch::ExpectedArg(
            0,
            vec![Type::Integer, Type::Float, Type::Boolean, Type::String],
            x.type_of(),
        ))),
        args => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn bool(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [x] => Ok(Object::from(x.truthy())),
        args => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn str(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::IntString(_)] => Ok(args[0].clone()),
        [Object::NatString(_)] => Ok(args[0].clone()),
        _ => Ok(Object::from(args[0].to_string().as_str())),
    }
}
