use std::str::FromStr;
use std::collections::HashMap;

use crate::error::Value;
use crate::object::{Object, List, Map, Builtin, Type, signature, IntVariant, Key};
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
    signature!(args = [x: str] {
        return Ok(Object::int(x.chars().count()))
    });

    signature!(args = [x: list] {
        return Ok(Object::int(x.len()))
    });

    signature!(args = [x: map] {
        return Ok(Object::int(x.len()))
    });

    signature!(args = [x: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::String, Type::List, Type::Map], x.type_of())))
    });

    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn range(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [start: int, stop: int] {
        return Ok((start.clone()..stop.clone()).map(Object::int).collect())
    });

    signature!(args = [x: any, _y: int] {
        return Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::Integer], x.type_of())))
    });

    signature!(args = [_x: any, y: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::Integer], y.type_of())))
    });

    signature!(args = [stop: int] {
        return Ok((IntVariant::from(0)..stop.clone()).map(Object::int).collect())
    });

    signature!(args = [x: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Integer], x.type_of())))
    });

    Err(Error::new(TypeMismatch::ArgCount(1, 2, args.len())))
}


pub fn int(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: int] {
        return Ok(Object::int(x.clone()))
    });

    signature!(args = [x: float] {
        return Ok(Object::int(x.round() as i64))
    });

    signature!(args = [x: bool] {
        return Ok(Object::int(if x { 1 } else { 0 }))
    });

    signature!(args = [x: str] {
        return Object::bigint(x).ok_or_else(
            || Error::new(Value::Convert(Type::Integer))
        ).map(|x| x.numeric_normalize())
    });

    signature!(args = [x: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Integer, Type::Float, Type::Boolean, Type::String], x.type_of())))
    });

    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn float(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: int] {
        return Ok(Object::float(x.to_f64()))
    });

    signature!(args = [x: float] {
        return Ok(Object::float(x))
    });

    signature!(args = [x: bool] {
        return Ok(Object::float(if x { 1.0 } else { 0.0 }))
    });

    signature!(args = [x: str] {
        return f64::from_str(x).map_err(
            |_| Error::new(Value::Convert(Type::Float))
        ).map(Object::float)
    });

    signature!(args = [x: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Integer, Type::Float, Type::Boolean, Type::String], x.type_of())))
    });

    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn bool(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: any] {
        return Ok(Object::bool(x.truthy()))
    });

    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn str(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: str] {
        return Ok(Object::str(x))
    });

    signature!(args = [x: any] {
        return Ok(Object::str(x.to_string()))
    });

    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn map(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [f: func, x: list] {
        let mut ret = List::new();
        for obj in x {
            let elt = f.call(&vec![obj.clone()], None)?;
            ret.push(elt);
        }
        return Ok(Object::list(ret))
    });

    signature!(args = [f: any, _x: list] {
        return Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Function], f.type_of())))
    });

    signature!(args = [_f: any, x: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::List], x.type_of())))
    });

    Err(Error::new(TypeMismatch::ArgCount(2, 2, args.len())))
}


pub fn filter(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [f: func, x: list] {
        let mut ret = List::new();
        for obj in x {
            let elt = f.call(&vec![obj.clone()], None)?;
            if elt.truthy() {
                ret.push(obj.clone());
            }
        }
        return Ok(Object::list(ret))
    });

    signature!(args = [f: any, _x: list] {
        return Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Function], f.type_of())))
    });

    signature!(args = [_f: any, x: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::List], x.type_of())))
    });

    Err(Error::new(TypeMismatch::ArgCount(2, 2, args.len())))
}


pub fn items(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: map] {
        let mut ret = List::new();
        for (key, val) in x {
            ret.push(Object::list(vec![
                Object::key(*key),
                val.clone()
            ]));
        }
        return Ok(Object::list(ret))
    });

    signature!(args = [x: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Map], x.type_of())))
    });

    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn exp(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: tofloat] {
        return Ok(Object::float(x.exp()))
    });

    signature!(args = [x: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Integer, Type::Float], x.type_of())))
    });

    signature!(args = [base: tofloat, exp: tofloat] {
        return Ok(Object::float(base.powf(exp)))
    });

    signature!(args = [x: any, _y: tofloat] {
        return Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Integer, Type::Float], x.type_of())))
    });

    signature!(args = [_x: any, y: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::Integer, Type::Float], y.type_of())))
    });

    Err(Error::new(TypeMismatch::ArgCount(1, 2, args.len())))
}


pub fn log(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: tofloat] {
        return Ok(Object::float(x.ln()))
    });

    signature!(args = [x: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Integer, Type::Float], x.type_of())))
    });

    signature!(args = [num: tofloat, base: tofloat] {
        return Ok(Object::float(num.log(base)))
    });

    signature!(args = [x: any, _y: tofloat] {
        return Err(Error::new(TypeMismatch::ExpectedArg(0, vec![Type::Integer, Type::Float], x.type_of())))
    });

    signature!(args = [_x: any, y: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::Integer, Type::Float], y.type_of())))
    });

    Err(Error::new(TypeMismatch::ArgCount(1, 2, args.len())))
}


pub fn ord(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: str] {
        let mut chars = x.chars();
        let c = chars.next();
        if c.is_none() || chars.next().is_some() {
            return Err(Error::new(Value::TooLong))
        }
        return Ok(Object::int(c.unwrap() as i64))
    });

    signature!(args = [x: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::String], x.type_of())));
    });

    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn chr(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: int] {
        let codepoint = u32::try_from(x).map_err(|_| Error::new(Value::OutOfRange))?;
        let c = char::try_from(codepoint).map_err(|_| Error::new(Value::OutOfRange))?;
        return Ok(Object::str(c.to_string()))
    });

    signature!(args = [x: any] {
        return Err(Error::new(TypeMismatch::ExpectedArg(1, vec![Type::Integer], x.type_of())));
    });

    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn isint(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: int] { return Ok(Object::bool(true)); });
    signature!(args = [_x: any] { return Ok(Object::bool(false)); });
    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn isstr(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: str] { return Ok(Object::bool(true)); });
    signature!(args = [_x: any] { return Ok(Object::bool(false)); });
    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn isnull(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: null] { return Ok(Object::bool(true)); });
    signature!(args = [_x: any] { return Ok(Object::bool(false)); });
    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn isbool(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: bool] { return Ok(Object::bool(true)); });
    signature!(args = [_x: any] { return Ok(Object::bool(false)); });
    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn isfloat(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: float] { return Ok(Object::bool(true)); });
    signature!(args = [_x: any] { return Ok(Object::bool(false)); });
    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn isnumber(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: float] { return Ok(Object::bool(true)); });
    signature!(args = [_x: int] { return Ok(Object::bool(true)); });
    signature!(args = [_x: any] { return Ok(Object::bool(false)); });
    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn isobject(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: map] { return Ok(Object::bool(true)); });
    signature!(args = [_x: any] { return Ok(Object::bool(false)); });
    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn islist(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: list] { return Ok(Object::bool(true)); });
    signature!(args = [_x: any] { return Ok(Object::bool(false)); });
    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}


pub fn isfunc(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: func] { return Ok(Object::bool(true)); });
    signature!(args = [_x: any] { return Ok(Object::bool(false)); });
    Err(Error::new(TypeMismatch::ArgCount(1, 1, args.len())))
}
