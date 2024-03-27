use std::borrow::Borrow;
use std::collections::HashMap;
use std::str::FromStr;

use crate::error::{Error, TypeMismatch, Types, Value};
use crate::object::Int;
use crate::types::{Key, List, Map, Builtin};
use crate::{Object, Type};

/// Convert a function by name to a [`Builtin`] object and append it to a
/// mapping.
///
/// ```ignore
/// fn myfunc(args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
///     todo!();
/// }
/// let mut map = HashMap::new();
/// builtin!(map, func)
/// // map["func"] is now available
/// ```
macro_rules! builtin {
    ($m: ident, $t: ident, $e: ident) => {
        let index = $t.len();
        $t.push(Builtin::new(
            $e,
            $crate::types::Key::new(stringify!($e).to_string()),
        ));
        $m.insert(stringify!($e), index);
    };
}

lazy_static! {
    /// Table of all builtin functions.
    pub static ref BUILTINS: (
        HashMap<&'static str, usize>,
        Vec<Builtin>,
    ) = {
        let mut m = HashMap::new();
        let mut t = Vec::new();
        builtin!(m, t, len);
        builtin!(m, t, range);
        builtin!(m, t, int);
        builtin!(m, t, float);
        builtin!(m, t, bool);
        builtin!(m, t, str);
        builtin!(m, t, map);
        builtin!(m, t, filter);
        builtin!(m, t, items);
        builtin!(m, t, exp);
        builtin!(m, t, log);
        builtin!(m, t, ord);
        builtin!(m, t, chr);
        builtin!(m, t, isint);
        builtin!(m, t, isstr);
        builtin!(m, t, isnull);
        builtin!(m, t, isbool);
        builtin!(m, t, isfloat);
        builtin!(m, t, isnumber);
        builtin!(m, t, isobject);
        builtin!(m, t, islist);
        builtin!(m, t, isfunc);
        (m, t)
    };
}

/// Return an error indicating wrong type of positional parameter.
///
/// ```ignore
/// expected_pos!(
///     index_of_parameter,
///     name_of_args_vector,
///     (allowed_types)...,
/// )
/// ```
macro_rules! expected_pos {
    ($index:expr, $name:ident, $($types:ident),*) => {
        return Err(Error::new(TypeMismatch::ExpectedPosArg {
            index: $index,
            allowed: Types::from(($(Type::$types),*)),
            received: $name.type_of(),
        }))
    };
}

/// Return an error indicating wrong type of keyword parameter.
///
/// ```ignore
/// expected_kw!(
///     name_of_parameter,
///     name_of_args_vector,
///     (allowed_types)...,
/// )
/// ```
macro_rules! expected_kw {
    ($name:expr, $kwargs:ident, $($types:ident),*) => {
        return Err(Error::new(TypeMismatch::ExpectedKwarg {
            name: Key::new(stringify!(name)),
            allowed: Types::from(($(Type::$types),*)),
            received: $name.type_of(),
        }))
    };
}

/// Return an error indicating wrong number of arguments.
///
/// ```ignore
/// argcount!(num_of_args, name_of_args_vector)
/// argcount!(
///     min_num_of_args,
///     max_num_of_args,
///     name_of_args_vector,
/// )
macro_rules! argcount {
    ($fixed:expr, $args:ident) => {
        return Err(Error::new(TypeMismatch::ArgCount {
            low: $fixed,
            high: $fixed,
            received: $args.len(),
        }))
    };
    ($low:expr, $high:expr, $args:ident) => {
        return Err(Error::new(TypeMismatch::ArgCount {
            low: $low,
            high: $high,
            received: $args.len(),
        }))
    };
}

/// Return the size of a collection or the length of a string.
fn len(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: str] {
        return Ok(Object::from(x.chars().count()))
    });

    signature!(args = [x: list] {
        return Ok(Object::from(x.len()))
    });

    signature!(args = [x: map] {
        return Ok(Object::from(x.len()))
    });

    signature!(args = [x: any] { expected_pos!(0, x, String, List, Map) });

    argcount!(1, args)
}

/// Works similarly to Python's function of the same name.
fn range(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [start: int, stop: int] {
        return Ok((start.clone()..stop.clone()).map(Object::from).collect())
    });

    signature!(args = [x: any, _y: int] { expected_pos!(0, x, Integer) });
    signature!(args = [_x: any, y: any] { expected_pos!(1, y, Integer) });

    signature!(args = [stop: int] {
        return Ok((Int::from(0)..stop.clone()).map(Object::from).collect())
    });

    signature!(args = [x: any] { expected_pos!(0, x, Integer) });

    argcount!(1, 2, args)
}

/// Convert the argument to an integer
fn int(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: int] {
        return Ok(Object::from(x.clone()))
    });

    signature!(args = [x: float] {
        return Ok(Object::from(x.round() as i64))
    });

    signature!(args = [x: bool] {
        return Ok(Object::from(if x { 1 } else { 0 }))
    });

    signature!(args = [x: str] {
        return Object::new_int_from_str(x).ok_or_else(
            || Error::new(Value::Convert(Type::Integer))
        );
    });

    signature!(args = [x: any] { expected_pos!(0, x, Integer, Float, Boolean, String) });

    argcount!(1, args)
}

/// Convert the argument to a float
fn float(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: int] {
        return Ok(Object::from(x.to_f64()))
    });

    signature!(args = [x: float] {
        return Ok(Object::from(x))
    });

    signature!(args = [x: bool] {
        return Ok(Object::from(if x { 1.0 } else { 0.0 }))
    });

    signature!(args = [x: str] {
        return f64::from_str(x).map_err(
            |_| Error::new(Value::Convert(Type::Float))
        ).map(Object::from)
    });

    signature!(args = [x: any] { expected_pos!(0, x, Integer, Float, Boolean, String) });

    argcount!(1, args)
}

/// Convert the argument to a bool (this never fails, see Gold's truthiness rules)
fn bool(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: any] {
        return Ok(Object::from(x.truthy()))
    });

    argcount!(1, args)
}

/// Convert the argument to a string
fn str(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: str] {
        return Ok(Object::from(x))
    });

    signature!(args = [x: any] {
        return Ok(Object::from(x.to_string()))
    });

    argcount!(1, args)
}

/// Map a function over a list. This can also be achieved in Gold with
///
/// ```ignore
/// [for x in y: f(x)]
/// ```
fn map(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [f: func, x: list] {
        let ret = Object::new_list();
        for obj in x.borrow().iter() {
            let elt = f.call(&vec![obj.clone()], None)?;
            ret.push_unchecked(elt);
        }
        return Ok(ret)
    });

    signature!(args = [f: any, _x: list] { expected_pos!(0, f, Function) });
    signature!(args = [_f: any, x: any] { expected_pos!(1, x, List) });

    argcount!(2, args)
}

/// Filter a list through a function. This can also be achieved in Gold with
///
/// ```ignore
/// [for x in y: when f(x): x]
/// ```
fn filter(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [f: func, x: list] {
        let ret = Object::new_list();
        for obj in x.borrow().iter() {
            let elt = f.call(&vec![obj.clone()], None)?;
            if elt.truthy() {
                ret.push_unchecked(obj.clone());
            }
        }
        return Ok(ret)
    });

    signature!(args = [f: any, _x: list] { expected_pos!(0, f, Function) });
    signature!(args = [_f: any, x: any] { expected_pos!(1, x, List) });

    argcount!(2, args)
}

/// Return a list of key-value pairs from a map.
fn items(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: map] {
        let ret = Object::new_list();
        for (key, val) in x.borrow().iter() {
            ret.push_unchecked(Object::from(vec![
                Object::from(*key),
                val.clone(),
            ]));
        }
        return Ok(ret)
    });

    signature!(args = [x: any] { expected_pos!(0, x, Map) });

    argcount!(1, args)
}

/// Compute the exponential function. This supports two signatures:
///
/// `exp(x)` is equivalent to `exp(x, base: 2.71828...)` while `exp(x, base: y)`
/// computes y to the power x (which is the same as `y^x`).
fn exp(args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [exp: tofloat] kwargs = {base: tofloat} {
        return Ok(Object::from(base.powf(exp)))
    });

    signature!(args = [_x: tofloat] kwargs = {base: any} { expected_kw!(base, kwargs, Integer, Float) });

    signature!(args = [x: tofloat] {
        return Ok(Object::from(x.exp()))
    });

    signature!(args = [x: any] { expected_pos!(0, x, Integer, Float) });

    argcount!(1, args)
}

/// Compute the logaritm. This supports two signatures:
///
/// `log(x)` is equivalent to `log(x, base: 2.71828...)` (the natural logarithm),
/// while `log(x, base: y)` computes the logarith of `x` to the base `y`.
fn log(args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [num: tofloat] kwargs = {base: tofloat} {
        return Ok(Object::from(num.log(base)))
    });

    signature!(args = [_x: tofloat] kwargs = {base: any} { expected_kw!(base, kwargs, Integer, Float) });

    signature!(args = [x: tofloat] {
        return Ok(Object::from(x.ln()))
    });

    signature!(args = [x: any] { expected_pos!(0, x, Integer, Float) });

    argcount!(1, args)
}

/// Return the unicode codepoint corresponding to a single-character string.
fn ord(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: str] {
        let mut chars = x.chars();
        let c = chars.next();
        if c.is_none() || chars.next().is_some() {
            return Err(Error::new(Value::TooLong))
        }
        return Ok(Object::from(c.unwrap() as i64))
    });

    signature!(args = [x: any] { expected_pos!(0, x, String) });

    argcount!(1, args)
}

/// Return the character (as a single-character string) that corresponds to
/// a unicode codepoint.
fn chr(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [x: int] {
        let codepoint = u32::try_from(x).map_err(|_| Error::new(Value::OutOfRange))?;
        let c = char::try_from(codepoint).map_err(|_| Error::new(Value::OutOfRange))?;
        return Ok(Object::from(c.to_string()))
    });

    signature!(args = [x: any] { expected_pos!(0, x, Integer) });

    argcount!(1, args)
}

/// Check whether the argument is an integer.
fn isint(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: int] { return Ok(Object::from(true)); });
    signature!(args = [_x: any] { return Ok(Object::from(false)); });
    argcount!(1, args)
}

/// Check whether the argument is a string.
fn isstr(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: str] { return Ok(Object::from(true)); });
    signature!(args = [_x: any] { return Ok(Object::from(false)); });
    argcount!(1, args)
}

/// Check whether the argument is null.
fn isnull(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: null] { return Ok(Object::from(true)); });
    signature!(args = [_x: any] { return Ok(Object::from(false)); });
    argcount!(1, args)
}

/// Check whether the argument is a boolean.
fn isbool(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: bool] { return Ok(Object::from(true)); });
    signature!(args = [_x: any] { return Ok(Object::from(false)); });
    argcount!(1, args)
}

/// Check whether the argument is a float.
fn isfloat(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: float] { return Ok(Object::from(true)); });
    signature!(args = [_x: any] { return Ok(Object::from(false)); });
    argcount!(1, args)
}

/// Check whether the argument is a number (integer or float).
fn isnumber(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: float] { return Ok(Object::from(true)); });
    signature!(args = [_x: int] { return Ok(Object::from(true)); });
    signature!(args = [_x: any] { return Ok(Object::from(false)); });
    argcount!(1, args)
}

/// Check whether the argument is an object (a mapping).
fn isobject(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: map] { return Ok(Object::from(true)); });
    signature!(args = [_x: any] { return Ok(Object::from(false)); });
    argcount!(1, args)
}

/// Check whether the argument is a list.
fn islist(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: list] { return Ok(Object::from(true)); });
    signature!(args = [_x: any] { return Ok(Object::from(false)); });
    argcount!(1, args)
}

/// Check whether the argument is a function.
fn isfunc(args: &List, _: Option<&Map>) -> Result<Object, Error> {
    signature!(args = [_x: func] { return Ok(Object::from(true)); });
    signature!(args = [_x: any] { return Ok(Object::from(false)); });
    argcount!(1, args)
}
