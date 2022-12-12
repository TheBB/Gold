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
        builtin!(m, map);
        builtin!(m, filter);
        builtin!(m, items);
        builtin!(m, exp);
        builtin!(m, log);
        builtin!(m, ord);
        builtin!(m, chr);
        builtin!(m, isint);
        builtin!(m, isstr);
        builtin!(m, isnull);
        builtin!(m, isbool);
        builtin!(m, isfloat);
        builtin!(m, isnumber);
        builtin!(m, isobject);
        builtin!(m, islist);
        builtin!(m, isfunc);
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
        [x] => Ok(Object::from(x.to_string().as_str())),
        args => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn map(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[1..] {
        [Object::List(x)] => {
            let mut ret = List::new();
            for obj in x.as_ref() {
                let elt = args[0].call(&vec![obj.clone()], None)?;
                ret.push(elt);
            }
            Ok(Object::from(ret))
        },
        [x] => Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::List], x.type_of()))),
        args => Err(Error::new(TypeMismatch::ArgCount(2, 2, args.len() + 1))),
    }
}


pub fn filter(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[1..] {
        [Object::List(x)] => {
            let mut ret = List::new();
            for obj in x.as_ref() {
                if args[0].call(&vec![obj.clone()], None)?.truthy() {
                    ret.push(obj.clone());
                }
            }
            Ok(Object::from(ret))
        },
        [x] => Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::List], x.type_of()))),
        args => Err(Error::new(TypeMismatch::ArgCount(2, 2, args.len() + 1))),
    }
}


pub fn items(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Map(x)] => {
            let mut ret = List::new();
            for (key, val) in x.as_ref() {
                ret.push(Object::from(vec![
                    Object::from(*key),
                    val.clone()
                ]));
            }
            Ok(Object::from(ret))
        },
        [x] => Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Map], x.type_of()))),
        args => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn exp(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    if args.len() != 1 && args.len() != 2 {
        return Err(Error::new(TypeMismatch::ArgCount(1, 2, args.len())));
    }

    let power = args[0].to_f64().ok_or_else(
        || Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Integer, Type::Float], args[0].type_of()))
    )?;

    let result = match &args[1..] {
        [Object::Float(x)] => x.powf(power),
        [Object::Integer(x)] => (*x as f64).powf(power),
        [Object::BigInteger(x)] => util::big_to_f64(x).powf(power),
        [x] => { return Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::Integer, Type::Float], x.type_of())))},
        [] => { power.exp() },

        // Unreachable
        _ => { 0.0 },
    };

    Ok(Object::from(result))
}


pub fn log(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    if args.len() != 1 && args.len() != 2 {
        return Err(Error::new(TypeMismatch::ArgCount(1, 2, args.len())));
    }

    let power = args[0].to_f64().ok_or_else(
        || Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Integer, Type::Float], args[0].type_of()))
    )?;

    let result = match &args[1..] {
        [Object::Float(x)] => power.log(*x),
        [Object::Integer(x)] => power.log(*x as f64),
        [Object::BigInteger(x)] => power.log(util::big_to_f64(x)),
        [x] => { return Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::Integer, Type::Float], x.type_of())))},
        [] => { power.ln() },

        // Unreachable
        _ => { 0.0 },
    };

    Ok(Object::from(result))
}


pub fn ord(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    let s = match &args[..] {
        [Object::IntString(x)] => x.as_str(),
        [Object::NatString(x)] => x.as_str(),
        [x] => { return Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::String], x.type_of()))); },
        _ => { return Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))); },
    };

    let mut chars = s.chars();
    let c = chars.next();

    if c.is_none() || chars.next().is_some() {
        return Err(Error::new(Value::TooLong))
    }

    Ok(Object::from(c.unwrap() as i64))
}


pub fn chr(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Integer(x)] => {
            let codepoint = u32::try_from(*x).map_err(|_| Error::new(Value::OutOfRange))?;
            let c = char::try_from(codepoint).map_err(|_| Error::new(Value::OutOfRange))?;
            Ok(Object::from(c.to_string().as_str()))
        },
        [Object::BigInteger(_)] => Err(Error::new(Value::OutOfRange)),
        [x] => Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::Integer], x.type_of()))),
        _ => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn isint(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Integer(_)] => Ok(Object::from(true)),
        [Object::BigInteger(_)] => Ok(Object::from(true)),
        [_] => Ok(Object::from(false)),
        _ => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn isstr(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::NatString(_)] => Ok(Object::from(true)),
        [Object::IntString(_)] => Ok(Object::from(true)),
        [_] => Ok(Object::from(false)),
        _ => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn isnull(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Null] => Ok(Object::from(true)),
        [_] => Ok(Object::from(false)),
        _ => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn isbool(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Boolean(_)] => Ok(Object::from(true)),
        [_] => Ok(Object::from(false)),
        _ => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn isfloat(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Float(_)] => Ok(Object::from(true)),
        [_] => Ok(Object::from(false)),
        _ => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn isnumber(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Integer(_)] => Ok(Object::from(true)),
        [Object::BigInteger(_)] => Ok(Object::from(true)),
        [Object::Float(_)] => Ok(Object::from(true)),
        [_] => Ok(Object::from(false)),
        _ => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn isobject(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Map(_)] => Ok(Object::from(true)),
        [_] => Ok(Object::from(false)),
        _ => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn islist(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::List(_)] => Ok(Object::from(true)),
        [_] => Ok(Object::from(false)),
        _ => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}


pub fn isfunc(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    match &args[..] {
        [Object::Function(_)] => Ok(Object::from(true)),
        [Object::Closure(_)] => Ok(Object::from(true)),
        [Object::Builtin(_)] => Ok(Object::from(true)),
        [_] => Ok(Object::from(false)),
        _ => Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len()))),
    }
}
