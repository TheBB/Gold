//! A Gold object is represented by the [`Object`] type. Internally an Object
//!
//! just wraps the [`ObjectVariant`] enumeration, which is hidden for
//! encapsulation purposes.
//!
//! The [`ObjectVariant`] type, in turn, has only unit wrappers for each of its
//! variants. Some of those variants are implemented in this module (e.g.
//! [`StrVariant`] for interned and non-interned string and [`IntVariant`] for
//! machine integers and bignums).
//!
//! User code should consider the internal structure of [`ObjectVariant`] and
//! all its variants to be unstable. Public methods on [`Object`] and
//! [`ObjectVariant`] (`Object` implements `Deref<ObjectVariant>`) are stable.

pub mod function;
pub mod integer;
pub mod string;

use std::cmp::Ordering;
use std::fmt::{Debug, Display};
use std::io::{Read, Write};
use std::str::FromStr;
use std::time::SystemTime;

#[cfg(feature = "python")]
use std::collections::HashMap;

#[cfg(feature = "python")]
use std::rc::Rc;

use gc::{Finalize, GcCellRef, GcCellRefMut, Trace};
use json::JsonValue;
use num_bigint::BigInt;
use rmp_serde::{decode, encode};
use serde::{Deserialize, Serialize};
use symbol_table::GlobalSymbol;

use crate::compile::CompiledFunction;
use crate::error::{Error, Internal, Reason, TypeMismatch, Value};
use crate::formatting::FormatSpec;
use crate::types::{Gc, GcCell};
use crate::{Key, List, Map, Type};
use crate::types::{UnOp, BinOp};

#[cfg(feature = "python")]
use crate::types::NativeClosure;

use function::Func;
use integer::Int;
use string::Str;

#[cfg(feature="python")]
use pyo3::{IntoPy, PyObject, Python, FromPyObject, PyAny, PyResult, PyErr, Py};

#[cfg(feature="python")]
use pyo3::types::{PyList, PyDict, PyTuple};

#[cfg(feature = "python")]
use pyo3::exceptions::PyTypeError;

/// The current serialization format version.
const SERIALIZE_VERSION: i32 = 1;


/// The object variant implements all possible variants of Gold objects,
/// although it's not the user-facing type, which is [`Object`], an opaque
/// struct enclosing an `ObjectVariant`.
#[derive(Clone, Debug, Serialize, Deserialize, Trace, Finalize)]
pub(crate) enum ObjV {
    /// Integers
    Int(#[unsafe_ignore_trace] Int),

    /// Floating-point numbers
    Float(f64),

    /// Strings
    Str(Str),

    /// Booleans
    Boolean(bool),

    /// Lists
    List(GcCell<List>),

    /// Mappings
    Map(GcCell<Map>),

    /// Functions
    Func(Func),

    /// Iterator
    ListIter(GcCell<usize>, GcCell<List>),

    /// Null
    Null,
}

// Utility macro for extracting a certain type from an object variant. Used for
// facilitating writing Gold functions in Rust.
macro_rules! extract {
    ($index:expr , $args:ident , str) => {
        $args.get($index).and_then(|x| x.get_str())
    };
    ($index:expr , $args:ident , int) => {
        $args.get($index).and_then(|x| x.get_int())
    };
    ($index:expr , $args:ident , float) => {
        $args.get($index).and_then(|x| x.get_float())
    };
    ($index:expr , $args:ident , bool) => {
        $args.get($index).and_then(|x| x.get_bool())
    };
    ($index:expr , $args:ident , list) => {
        $args.get($index).and_then(|x| x.get_list())
    };
    ($index:expr , $args:ident , map) => {
        $args.get($index).and_then(|x| x.get_map())
    };
    ($index:expr , $args:ident , func) => {
        $args.get($index).and_then(|x| x.get_func())
    };
    ($index:expr , $args:ident , null) => {
        $args.get($index).and_then(|x| x.get_null())
    };

    ($index:expr , $args:ident , any) => {
        $args.get($index)
    };

    ($index:expr , $args:ident , tofloat) => {
        $args.get($index).and_then(|x| x.get_float()).or_else(|| {
            $args
                .get($index)
                .and_then(|x| x.get_int().map(|x| x.to_f64()))
        })
    };
}

macro_rules! extractkw {
    ($kwargs:ident , $key:ident , any) => {
        $kwargs.and_then(|kws| kws.get(&$crate::Key::from(stringify!($key))))
    };

    ($kwargs:ident , $key:ident , tofloat) => {{
        let key = $crate::Key::from(stringify!($key));
        $kwargs.and_then(|kws| {
            kws.get(&key)
                .and_then(|x| x.get_float())
                .or_else(|| kws.get(&key).and_then(|x| x.get_int().map(|x| x.to_f64())))
        })
    }};
}

/// Utility macro for capturing a certain calling convention. Used for writing
/// Gold functions in Rust.
///
/// ```ignore
/// signature!(args = [x: int, y: float] {
///     // function body
/// })
/// ```
///
/// The function body is executed if the list `args` matches the given types.
/// The number and types of the arguments must be exact. If the arguments don't
/// match, or if the function body does not return, evaluation proceeds. You can
/// therefore call this macro multiple times in succession to match different
/// calling conventions.
#[macro_export]
macro_rules! signature {
    // Entry point pattern
    ($args:ident = [ $($param:ident : $type:ident),* ] $kwargs:ident = { $($kw:ident : $kwtype:ident),* } $block:block) => {
        signature!(0 ; $args [ $($param : $type),* ] , $kwargs [ $($kw : $kwtype),* ] , $block)
    };

    // Entry point pattern, no kwargs
    ($args:ident = [ $($param:ident : $type:ident),* ] $block:block) => {
        signature!(0 ; $args [ $($param : $type),* ] , missing [ ] , $block)
    };

    ($index:expr ; $args:ident [ $param:ident : $type:ident , $($params:ident : $types:ident),+ ] , $kwargs:ident [ $($kw:ident : $kwtype:ident),* ] , $block:block) => {
        if let Some($param) = extract!($index, $args, $type) {
            signature!($index + 1 ; $args [ $($params : $types),* ] , $kwargs [ $($kw : $kwtype),* ] , $block)
        }
    };

    ($index:expr ; $args:ident [ $param:ident : $type:ident ] , $kwargs:ident [ $($kw:ident : $kwtype:ident),* ] , $block:block) => {
        if let Some($param) = extract!($index, $args, $type) {
            signature!($index + 1 ; $args [ ] , $kwargs [ $($kw : $kwtype),* ] , $block)
        }
    };

    ($index:expr ; $args:ident [ ] , $kwargs:ident [ $kw:ident : $kwtype:ident ($kws:ident : $kwtypes:ident),+ ] , $block:block) => {
        if let Some($kw) = extractkw!($kwargs, $kw, $kwtype) {
            signature!($index ; $args [ ] , $kwargs [ $($kws : $kwtypes),* ] , $block)
        }
    };

    ($index:expr ; $args:ident [ ] , $kwargs:ident [ $kw:ident : $kwtype:ident ] , $block:block) => {
        if let Some($kw) = extractkw!($kwargs, $kw, $kwtype) {
            signature!($index ; $args [ ] , $kwargs [ ] , $block)
        }
    };

    ($index:expr ; $args:ident [ ] , $kwargs:ident [ ] , $block:block) => {
        if $args.len() == $index $block
    };
}

pub use signature;

/// The general type of Gold objects.
///
/// While this type wraps [`ObjectVariant`], a fact which can be revealed using
/// the [`Object::variant`] method, this should be considered an implementation
/// detail.
///
/// `Object` is `Deref<ObjectVariant>`, so supports all methods defined there.
#[derive(Clone, Debug, Serialize, Deserialize, Trace, Finalize)]
pub struct Object(pub(crate) ObjV);

// FuncVariant doesn't implement PartialEq, so this has to be done manually.
impl PartialEq<Object> for Object {
    fn eq(&self, other: &Object) -> bool {
        let Self(this) = self;
        let Self(that) = other;
        match (this, that) {
            (ObjV::Int(x), ObjV::Int(y)) => x.eq(y),
            (ObjV::Float(x), ObjV::Float(y)) => x.eq(y),
            (ObjV::Str(x), ObjV::Str(y)) => x.eq(y),
            (ObjV::Boolean(x), ObjV::Boolean(y)) => x.eq(y),
            (ObjV::List(x), ObjV::List(y)) => x.eq(y),
            (ObjV::Map(x), ObjV::Map(y)) => x.eq(y),
            (ObjV::Null, ObjV::Null) => true,
            _ => false,
        }
    }
}

impl PartialOrd<Object> for Object {
    fn partial_cmp(&self, other: &Object) -> Option<Ordering> {
        let Self(this) = self;
        let Self(that) = other;
        match (this, that) {
            (ObjV::Int(x), ObjV::Int(y)) => x.partial_cmp(y),
            (ObjV::Int(x), ObjV::Float(y)) => x.partial_cmp(y),
            (ObjV::Float(x), ObjV::Int(y)) => y.partial_cmp(x).map(Ordering::reverse),
            (ObjV::Float(x), ObjV::Float(y)) => x.partial_cmp(y),
            (ObjV::Str(x), ObjV::Str(y)) => x.partial_cmp(y),
            _ => None,
        }
    }
}

impl Object {
    // Constructors
    // ------------------------------------------------------------------------------------------------

    /// Construct an interned string.
    pub fn new_str_interned<T>(val: T) -> Self where Key: From<T> {
        Self(ObjV::Str(Str::interned(val)))
    }

    /// Construct a non-interned string.
    pub fn new_str_natural(val: impl AsRef<str>) -> Self {
        Self(ObjV::Str(Str::natural(val)))
    }

    /// Construct a string, deciding based on length whether to intern or not.
    pub fn new_str<T>(val: T) -> Self where Key: From<T>, T: AsRef<str> {
        if val.as_ref().len() < 20 {
            Self::new_str_interned(val)
        } else {
            Self::new_str_natural(val)
        }
    }

    /// Construct an integer.
    pub(crate) fn new_int<T>(val: T) -> Self where Int: From<T> {
        Self(ObjV::Int(Int::from(val)))
    }

    /// Construct a big integer from a decimal string representation.
    pub fn new_int_from_str(x: impl AsRef<str>) -> Option<Self> {
        i64::from_str(x.as_ref()).ok().map(Self::from).or_else(
            || BigInt::from_str(x.as_ref()).ok().map(Self::from)
        )
    }

    /// Construct an empty list.
    pub fn new_list() -> Self {
        Self(ObjV::List(GcCell::new(vec![])))
    }

    /// Construct an empty map.
    pub fn new_map() -> Self {
        Self(ObjV::Map(GcCell::new(Map::new())))
    }

    // Mutation
    // ------------------------------------------------------------------------------------------------

    pub(crate) fn push(&self, other: Object) -> Result<(), Error> {
        let Self(this) = self;
        match this {
            ObjV::List(x) => {
                let mut xx = x.borrow_mut();
                xx.push(other);
                Ok(())
            }
            _ => Err(Error::new(Reason::None)),
        }
    }

    pub(crate) fn push_unchecked(&self, other: Object) {
        self.push(other).unwrap();
    }

    pub(crate) fn push_cell(&self, other: GcCell<Object>) -> Result<(), Error> {
        let Self(this) = self;
        match this {
            ObjV::Func(func) => { func.push_cell(other) },
            _ => Err(Error::new(Reason::None)),
        }
    }

    pub(crate) fn insert(&self, key: Self, value: Self) -> Result<(), Error> {
        self.insert_key(
            key.get_key()
                .ok_or_else(|| Error::new(TypeMismatch::MapKey(key.type_of())))?,
            value,
        )
    }

    pub(crate) fn insert_key(&self, key: Key, value: Object) -> Result<(), Error> {
        let Self(this) = self;
        match this {
            ObjV::Map(x) => {
                let mut xx = x.borrow_mut();
                xx.insert(key, value);
                Ok(())
            }
            _ => Err(Error::new(Reason::None)),
        }
    }

    pub(crate) fn append(&self, mut it: impl Iterator<Item = Object>) -> Result<(), Error> {
        let Self(this) = self;
        match this {
            ObjV::List(x) => {
                let mut xx = x.borrow_mut();
                while let Some(obj) = it.next() {
                    xx.push(obj);
                }
                Ok(())
            }
            _ => Err(Error::new(Reason::None)),
        }
    }

    // Unchecked functions
    // ------------------------------------------------------------------------------------------------

    /// Mathematical negation.
    pub fn neg(&self) -> Result<Self, Error> {
        let Self(this) = self;
        match this {
            ObjV::Int(x) => Ok(Self(ObjV::Int(x.neg()))),
            ObjV::Float(x) => Ok(Self(ObjV::Float(-x))),
            _ => Err(Error::new(TypeMismatch::UnOp(
                self.type_of(),
                UnOp::ArithmeticalNegate,
            ))),
        }
    }

    /// String representation of this object. Used for string interpolation.
    pub fn format(&self, spec: &FormatSpec) -> Result<String, Error> {
        let Self(this) = self;
        match this {
            ObjV::Str(r) => {
                if let Some(str_spec) = spec.string_spec() {
                    Ok(str_spec.format(r.as_str()))
                } else {
                    Err(Error::new(TypeMismatch::InterpolateSpec(self.type_of())))
                }
            }
            ObjV::Boolean(x) => {
                if let Some(str_spec) = spec.string_spec() {
                    let s = if *x { "true" } else { "false" };
                    Ok(str_spec.format(s))
                } else if let Some(int_spec) = spec.integer_spec() {
                    let i = if *x { 1 } else { 0 };
                    int_spec.format(&Int::from(i))
                } else if let Some(float_spec) = spec.float_spec() {
                    let f = if *x { 1.0 } else { 0.0 };
                    Ok(float_spec.format(f))
                } else {
                    Err(Error::new(TypeMismatch::InterpolateSpec(self.type_of())))
                }
            }
            ObjV::Null => {
                if let Some(str_spec) = spec.string_spec() {
                    Ok(str_spec.format("null"))
                } else {
                    Err(Error::new(TypeMismatch::InterpolateSpec(self.type_of())))
                }
            }
            ObjV::Int(r) => {
                if let Some(int_spec) = spec.integer_spec() {
                    int_spec.format(r)
                } else if let Some(float_spec) = spec.float_spec() {
                    Ok(float_spec.format(r.to_f64()))
                } else {
                    Err(Error::new(TypeMismatch::InterpolateSpec(self.type_of())))
                }
            }
            ObjV::Float(r) => {
                if let Some(float_spec) = spec.float_spec() {
                    Ok(float_spec.format(*r))
                } else {
                    Err(Error::new(TypeMismatch::InterpolateSpec(self.type_of())))
                }
            }
            _ => Err(Error::new(TypeMismatch::Interpolate(self.type_of()))),
        }
    }

    pub(crate) fn closure(val: CompiledFunction) -> Self {
        Self(ObjV::Func(Func::closure(val)))
    }

    /// Construct a string directly from an interned symbol.
    pub fn key(val: Key) -> Self {
        Self(ObjV::Str(Str::interned(val)))
    }

    /// Construct a float.
    pub fn float(val: f64) -> Self {
        Self(ObjV::Float(val))
    }

    /// Construct a boolean.
    pub fn bool(val: bool) -> Self {
        Self(ObjV::Boolean(val))
    }

    /// Return the null object.
    pub fn null() -> Self {
        Self(ObjV::Null)
    }

    /// Construct a function.
    pub(crate) fn func<T>(val: T) -> Self
    where
        Func: From<T>,
    {
        Self(ObjV::Func(Func::from(val)))
    }

    /// Construct an iterator
    pub fn iterator(obj: &Object) -> Result<Self, Error> {
        if let Object(ObjV::List(l)) = obj {
            Ok(Object(ObjV::ListIter(
                GcCell::new(0),
                l.clone(),
            )))
        } else {
            Err(Error::new(TypeMismatch::Iterate(obj.type_of())))
        }
    }

    /// Get next value from an iterator
    pub fn next(&self) -> Result<Option<Self>, Error> {
        if let Object(ObjV::ListIter(index_cell, list)) = self {
            let mut index_cell_ref = index_cell.borrow_mut();
            let l = list.borrow();
            if *index_cell_ref < l.len() {
                let obj = l[*index_cell_ref].clone();
                *index_cell_ref += 1;
                Ok(Some(obj))
            } else {
                Ok(None)
            }
        } else {
            Err(Error::new(Reason::None))
        }
    }

    /// Serialize this objcet to a byte vector.
    pub fn serialize(&self) -> Option<Vec<u8>> {
        let data = (SERIALIZE_VERSION, SystemTime::now(), self);
        encode::to_vec(&data).ok()
    }

    /// Serialize this objcet to a writable buffer.
    pub fn serialize_write<T: Write + ?Sized>(&self, out: &mut T) -> Option<()> {
        let data = (SERIALIZE_VERSION, SystemTime::now(), self);
        encode::write(out, &data).ok()
    }

    /// Deserialize an object from a byte vector.
    pub fn deserialize(data: &Vec<u8>) -> Option<(Self, SystemTime)> {
        let (version, time, retval) =
            decode::from_slice::<(i32, SystemTime, Self)>(data.as_slice()).ok()?;
        if version < SERIALIZE_VERSION {
            None
        } else {
            Some((retval, time))
        }
    }

    /// Deserialize an object from a readable buffer.
    pub fn deserialize_read<T: Read>(data: T) -> Option<(Self, SystemTime)> {
        let (version, time, retval) = decode::from_read::<T, (i32, SystemTime, Self)>(data).ok()?;
        if version < SERIALIZE_VERSION {
            None
        } else {
            Some((retval, time))
        }
    }

    /// Get the type of this object.
    pub fn type_of(&self) -> Type {
        let Self(this) = self;
        match this {
            ObjV::Int(_) => Type::Integer,
            ObjV::Float(_) => Type::Float,
            ObjV::Str(_) => Type::String,
            ObjV::Boolean(_) => Type::Boolean,
            ObjV::List(_) => Type::List,
            ObjV::Map(_) => Type::Map,
            ObjV::Func(_) => Type::Function,
            ObjV::ListIter(_, _) => Type::Iterator,
            ObjV::Null => Type::Null,
        }
    }

    /// User-facing (non-structural) equality.
    ///
    /// We use a stricter form of equality checking for testing purposes. This
    /// method implements equality under Gold semantics.
    pub fn user_eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            // Equality between disparate types
            (ObjV::Float(x), ObjV::Int(y)) => y.eq(x),
            (ObjV::Int(x), ObjV::Float(y)) => x.eq(y),

            // Structural equality
            (ObjV::Int(x), ObjV::Int(y)) => x.user_eq(y),
            (ObjV::Float(x), ObjV::Float(y)) => x.eq(y),
            (ObjV::Str(x), ObjV::Str(y)) => x.user_eq(y),
            (ObjV::Boolean(x), ObjV::Boolean(y)) => x.eq(y),
            (ObjV::Null, ObjV::Null) => true,
            (ObjV::Func(x), ObjV::Func(y)) => x.user_eq(y),

            // Composite objects: we must implement equality the hard way, since
            // `eq` would not delegate to checking contained objects using
            // `user_eq`.
            (ObjV::List(x), ObjV::List(y)) => {
                let xx = x.borrow();
                let yy = y.borrow();
                if xx.len() != yy.len() {
                    return false;
                }
                for (xx, yy) in xx.iter().zip(yy.iter()) {
                    if !xx.user_eq(yy) {
                        return false;
                    }
                }
                true
            }

            (ObjV::Map(x), ObjV::Map(y)) => {
                let xx = x.borrow();
                let yy = y.borrow();
                if xx.len() != yy.len() {
                    return false;
                }
                for (xk, xv) in xx.iter() {
                    if let Some(yv) = yy.get(xk) {
                        if !xv.user_eq(yv) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                true
            }

            // Different types generally mean not equal
            _ => false,
        }
    }

    /// Extract the string variant if applicable.
    pub fn get_str(&self) -> Option<&str> {
        match &self.0 {
            ObjV::Str(x) => Some(x.as_str()),
            _ => None,
        }
    }

    /// Extract the integer variant if applicable.
    pub(crate) fn get_int(&self) -> Option<&Int> {
        match &self.0 {
            ObjV::Int(x) => Some(x),
            _ => None,
        }
    }

    /// Extract the floating-point variant if applicable.
    pub fn get_float(&self) -> Option<f64> {
        match &self.0 {
            ObjV::Float(x) => Some(*x),
            _ => None,
        }
    }

    /// Extract the bool variant if applicable. (See also [`ObjectVariant::truthy`].)
    pub fn get_bool(&self) -> Option<bool> {
        match &self.0 {
            ObjV::Boolean(x) => Some(*x),
            _ => None,
        }
    }

    /// Extract the list variant if applicable.
    pub fn get_list<'a>(&'a self) -> Option<GcCellRef<'_, List>> {
        match &self.0 {
            ObjV::List(x) => Some(x.borrow()),
            _ => None,
        }
    }

    /// Extract the map variant if applicable.
    pub(crate) fn get_map<'a>(&'a self) -> Option<GcCellRef<'_, Map>> {
        match &self.0 {
            ObjV::Map(x) => Some(x.borrow()),
            _ => None,
        }
    }

    /// Extract the map variant if applicable.
    pub(crate) fn get_map_mut<'a>(&'a self) -> Option<GcCellRefMut<'_, Map>> {
        match &self.0 {
            ObjV::Map(x) => Some(x.borrow_mut()),
            _ => None,
        }
    }

    /// Extract the function variant if applicable.
    #[cfg(feature = "python")]
    pub(crate) fn get_func_variant<'a>(&'a self) -> Option<&'a Func> {
        match &self.0 {
            ObjV::Func(func) => Some(func),
            _ => None,
        }
    }

    /// Extract the key variant if applicable (an interned string).
    pub fn get_key(&self) -> Option<Key> {
        match &self.0 {
            ObjV::Str(x) => Some(Key::from(x)),
            _ => None,
        }
    }

    /// Extract the function variant if applicable.
    pub(crate) fn get_func(&self) -> Option<&Func> {
        match &self.0 {
            ObjV::Func(x) => Some(x),
            _ => None,
        }
    }

    /// Extract the null variant if applicable.
    ///
    /// Note that `obj.get_null().is_some() == obj.is_null()`.
    pub fn get_null(&self) -> Option<()> {
        match &self.0 {
            ObjV::Null => Some(()),
            _ => None,
        }
    }

    /// Check whether the object is null.
    pub fn is_null(&self) -> bool {
        match &self.0 {
            ObjV::Null => true,
            _ => false,
        }
    }

    pub(crate) fn native_callable(&self) -> Option<&dyn Fn(&List, Option<&Map>) -> Result<Object, Error>> {
        let Self(this) = self;
        match this {
            ObjV::Func(func) => func.native_callable(),
            _ => None,
        }
    }

    pub(crate) fn get_closure(&self) -> Option<(Gc<CompiledFunction>, GcCell<Vec<GcCell<Object>>>)> {
        let Self(this) = self;
        match this {
            ObjV::Func(func) => func.get_closure(),
            _ => None,
        }
    }

    /// The function call operator.
    #[cfg(feature = "python")]
    pub(crate) fn call(&self, args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
        match self.get_func_variant() {
            Some(func) => func.call(args, kwargs),
            None => return Err(Error::new(TypeMismatch::Call(self.type_of()))),
        }
    }

    /// Check whether this object is truthy, as interpreted by if-then-else
    /// expressions.
    ///
    /// Every object is truthy except for null, false and zeros. In particular,
    /// empty collections are truthy!
    pub fn truthy(&self) -> bool {
        match &self.0 {
            ObjV::Null => false,
            ObjV::Boolean(val) => *val,
            ObjV::Int(r) => r.nonzero(),
            ObjV::Float(r) => *r != 0.0,
            _ => true,
        }
    }

    /// Return `Some(true)` if `self` and `other` are comparable and that the
    /// comparison is equal to `ordering`. Returns `Some(false)` if it is not.
    /// Returns `None` if they are not comparable.
    pub fn cmp_bool(&self, other: &Self, ordering: Ordering) -> Option<bool> {
        self.partial_cmp(other).map(|x| x == ordering)
    }

    /// The indexing operator (for both lists and maps).
    pub fn index(&self, other: &Object) -> Result<Object, Error> {
        match (&self.0, &other.0) {
            (ObjV::List(x), ObjV::Int(y)) => {
                let xx = x.borrow();
                let i: usize = y.try_into().map_err(|_| Error::new(Value::OutOfRange))?;
                if i >= xx.len() {
                    Err(Error::new(Value::OutOfRange))
                } else {
                    Ok(xx[i].clone())
                }
            }
            (ObjV::Map(x), ObjV::Str(y)) => {
                let xx = x.borrow();
                let yy = GlobalSymbol::from(y);
                xx.get(&yy)
                    .ok_or_else(|| Error::new(Reason::Unassigned(yy)))
                    .map(Object::clone)
            }
            _ => Err(Error::new(TypeMismatch::BinOp(
                self.type_of(),
                other.type_of(),
                BinOp::Index,
            ))),
        }
    }

    /// The containment operator.
    pub fn contains(&self, other: &Object) -> Result<bool, Error> {
        let Self(this) = self;
        let Self(that) = other;

        if let ObjV::List(x) = this {
            return Ok(x.borrow().contains(other));
        }

        if let (ObjV::Str(haystack), ObjV::Str(needle)) = (this, that) {
            return Ok(haystack.as_str().contains(needle.as_str()));
        }

        Err(Error::new(TypeMismatch::BinOp(
            self.type_of(),
            other.type_of(),
            BinOp::Contains,
        )))
    }

    pub(crate) fn splat_into(&self, other: Object) -> Result<(), Error> {
        let Self(this) = self;
        let Self(that) = &other;
        match (this, that) {
            (ObjV::List(x), ObjV::List(y)) => {
                let mut xx = x.borrow_mut();
                let yy = y.borrow();
                xx.extend_from_slice(&*yy);
                Ok(())
            }

            (ObjV::List(_), _) => Err(Error::new(TypeMismatch::SplatList(other.type_of()))),

            (ObjV::Map(x), ObjV::Map(y)) => {
                let mut xx = x.borrow_mut();
                let yy = y.borrow();
                for (k, v) in yy.iter() {
                    xx.insert(k.clone(), v.clone());
                }
                Ok(())
            }

            (ObjV::Map(_), _) => Err(Error::new(TypeMismatch::SplatMap(other.type_of()))),

            _ => Err(Error::new(Internal::SplatToNonCollection)),
        }
    }

    /// Universal utility method for implementing mathematical operators.
    ///
    /// If both operands are integer variants, the `ixi` function is applied. If
    /// either operand is not an integer, both operands are converted to floats
    /// and the `fxf` function is applied.
    ///
    /// In case of type mismatch, an error is reported using `op`.
    fn operate<S, T>(
        &self,
        other: &Self,
        ixi: impl Fn(&Int, &Int) -> S,
        fxf: impl Fn(f64, f64) -> T,
        op: BinOp,
    ) -> Result<Self, Error>
    where
        Self: From<S> + From<T>,
    {
        let Self(this) = self;
        let Self(that) = other;
        match (this, that) {
            (ObjV::Int(xx), ObjV::Int(yy)) => Ok(Self::from(ixi(xx, yy))),
            (ObjV::Int(xx), ObjV::Float(yy)) => Ok(Self::from(fxf(xx.to_f64(), *yy))),
            (ObjV::Float(xx), ObjV::Int(yy)) => Ok(Self::from(fxf(*xx, yy.to_f64()))),
            (ObjV::Float(xx), ObjV::Float(yy)) => Ok(Self::from(fxf(*xx, *yy))),

            _ => Err(Error::new(TypeMismatch::BinOp(
                self.type_of(),
                other.type_of(),
                op,
            ))),
        }
    }

    /// The plus operator: concatenate strings and lists, or delegate to mathematical addition.
    pub fn add(&self, other: &Self) -> Result<Self, Error> {
        let Self(this) = self;
        let Self(that) = other;
        match (this, that) {
            (ObjV::List(x), ObjV::List(y)) => {
                let result = Self::new_list();
                result.append(x.borrow().iter().chain(y.borrow().iter()).cloned())?;
                Ok(result)
            }
            (ObjV::Str(x), ObjV::Str(y)) => Ok(Self(ObjV::Str(x.add(y)))),
            _ => self.operate(other, Int::add, |x, y| x + y, BinOp::Add),
        }
    }

    /// The minus operator: mathematical subtraction.
    pub fn sub(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, Int::sub, |x, y| x - y, BinOp::Subtract)
    }

    /// The asterisk operator: mathematical multiplication.
    pub fn mul(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, Int::mul, |x, y| x * y, BinOp::Multiply)
    }

    /// The slash operator: mathematical division.
    pub fn div(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, Int::div, |x, y| x / y, BinOp::Divide)
    }

    /// The double slash operator: integer division.
    pub fn idiv(&self, other: &Self) -> Result<Self, Error> {
        self.operate(
            other,
            Int::idiv,
            |x, y| (x / y).floor() as f64,
            BinOp::IntegerDivide,
        )
    }

    /// Convert to f64 if possible.
    pub fn to_f64(&self) -> Option<f64> {
        let Self(this) = self;
        match this {
            ObjV::Int(x) => Some(x.to_f64()),
            ObjV::Float(x) => Some(*x),
            _ => None,
        }
    }

    /// The exponentiation operator. This uses [`IntVariant::pow`] if both
    /// operands are integers and if the exponent is non-negative. Otherwise it
    /// delegates to floating-point exponentiation.
    pub fn pow(&self, other: &Self) -> Result<Self, Error> {
        let Self(this) = self;
        let Self(that) = other;

        if let (ObjV::Int(x), ObjV::Int(y)) = (this, that) {
            if let Some(r) = x.pow(y) {
                return Ok(Self::from(r));
            }
        }

        let (xx, yy) = self
            .to_f64()
            .and_then(|x| other.to_f64().map(|y| (x, y)))
            .ok_or_else(|| {
                Error::new(TypeMismatch::BinOp(
                    self.type_of(),
                    other.type_of(),
                    BinOp::Power,
                ))
            })?;
        Ok(Self::from(xx.powf(yy)))
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(this) = self;
        match this {
            ObjV::Str(r) => f.write_fmt(format_args!("{}", r)),
            ObjV::Int(r) => f.write_fmt(format_args!("{}", r)),
            ObjV::Float(r) => f.write_fmt(format_args!("{}", r)),
            ObjV::Boolean(true) => f.write_str("true"),
            ObjV::Boolean(false) => f.write_str("false"),
            ObjV::Null => f.write_str("null"),

            ObjV::List(elements) => {
                f.write_str("[")?;
                let temp = elements.borrow();
                let mut iter = temp.iter().peekable();
                while let Some(element) = iter.next() {
                    f.write_fmt(format_args!("{}", element))?;
                    if iter.peek().is_some() {
                        f.write_str(", ")?;
                    }
                }
                f.write_str("]")
            }

            ObjV::Map(elements) => {
                f.write_str("{")?;
                let temp = elements.borrow();
                let mut iter = temp.iter().peekable();
                while let Some((k, v)) = iter.next() {
                    f.write_fmt(format_args!("{}: {}", k, v))?;
                    if iter.peek().is_some() {
                        f.write_str(", ")?;
                    }
                }
                f.write_str("}")
            }

            _ => f.write_str("?"),
        }
    }
}

impl From<bool> for Object {
    fn from(value: bool) -> Self {
        Object::bool(value)
    }
}

impl From<&str> for Object {
    fn from(value: &str) -> Self {
        Object::new_str(value)
    }
}

impl From<Key> for Object {
    fn from(value: Key) -> Self {
        Object::key(value)
    }
}

impl<T> From<T> for Object
where
    Int: From<T>,
{
    fn from(value: T) -> Self {
        Self(ObjV::Int(Int::from(value)))
    }
}

impl From<f64> for Object {
    fn from(x: f64) -> Self {
        Self(ObjV::Float(x))
    }
}

impl From<List> for Object {
    fn from(value: List) -> Self {
        Self(ObjV::List(GcCell::new(value)))
    }
}

impl From<Vec<(&str, Object)>> for Object {
    fn from(value: Vec<(&str, Object)>) -> Self {
        let ret = Self::new_map();
        for (k, v) in value {
            ret.insert_key(Key::new(k), v).unwrap();
        }
        ret
    }
}

impl From<Map> for Object {
    fn from(value: Map) -> Self {
        Self(ObjV::Map(GcCell::new(value)))
    }
}

impl FromIterator<Object> for Object {
    fn from_iter<T: IntoIterator<Item = Object>>(iter: T) -> Self {
        Object(ObjV::List(GcCell::new(
            iter.into_iter().collect(),
        )))
    }
}

impl TryFrom<Object> for JsonValue {
    type Error = Error;

    fn try_from(value: Object) -> Result<Self, Self::Error> {
        JsonValue::try_from(&value)
    }
}

impl TryFrom<&Object> for JsonValue {
    type Error = Error;

    fn try_from(value: &Object) -> Result<Self, Self::Error> {
        let Object(this) = value;
        match this {
            ObjV::Int(x) => i64::try_from(x)
                .map_err(|_| Error::new(Value::TooLarge))
                .map(JsonValue::from),
            ObjV::Float(x) => Ok(JsonValue::from(*x)),
            ObjV::Str(x) => Ok(JsonValue::from(x.as_str())),
            ObjV::Boolean(x) => Ok(JsonValue::from(*x)),
            ObjV::List(x) => {
                let mut val = JsonValue::new_array();
                for element in x.borrow().iter() {
                    val.push(JsonValue::try_from(element)?).unwrap();
                }
                Ok(val)
            }
            ObjV::Map(x) => {
                let mut val = JsonValue::new_object();
                for (key, element) in x.borrow().iter() {
                    val[key.as_str()] = JsonValue::try_from(element)?;
                }
                Ok(val)
            }
            ObjV::Null => Ok(JsonValue::Null),
            _ => Err(Error::new(TypeMismatch::Json(value.type_of()))),
        }
    }
}

#[cfg(feature = "python")]
impl<'s> FromPyObject<'s> for Object {
    fn extract(obj: &'s PyAny) -> PyResult<Self> {
        // Nothing magical here, just a prioritized list of possible Python types and their Gold equivalents
        if let Ok(x) = obj.extract::<Func>() {
            Ok(Object::func(x))
        } else if let Ok(x) = obj.extract::<i64>() {
            Ok(Object::new_int(x))
        } else if let Ok(x) = obj.extract::<BigInt>() {
            Ok(Object::new_int(x))
        } else if let Ok(x) = obj.extract::<f64>() {
            Ok(Object::from(x))
        } else if let Ok(x) = obj.extract::<&str>() {
            Ok(Object::from(x))
        } else if let Ok(x) = obj.extract::<bool>() {
            Ok(Object::from(x))
        } else if let Ok(x) = obj.extract::<List>() {
            Ok(Object::from(x))
        } else if let Ok(x) = obj.extract::<HashMap<String, Object>>() {
            Ok(Object::from(Map::from_iter(x.into_iter().map(|(k,v)| (Key::new(k), v)))))
        } else if obj.is_none() {
            Ok(Object::null())
        } else if obj.is_callable() {
            let func: Py<PyAny> = obj.into();
            let closure: Rc<NativeClosure> = Rc::new(move |args: &List, kwargs: Option<&Map>| {
                let result = Python::with_gil(|py| {
                    let a = PyTuple::new(py, args.iter().map(|x| x.clone().into_py(py)));
                    let b = PyDict::new(py);
                    if let Some(kws) = kwargs {
                        for (k, v) in kws {
                            b.set_item(k.as_str(), v.clone().into_py(py))?;
                        }
                    }
                    let result = func.call(py, a, Some(b))?.extract::<Object>(py)?;
                    Ok(result)
                });
                result.map_err(|e: PyErr| Error::new(Reason::External(format!("{}", e))))
            });
            Ok(Object::func(closure))
        } else {
            Err(PyTypeError::new_err(format!(
                "uncovertible type: {}",
                obj.get_type().name().unwrap_or("unknown")
            )))
        }
    }
}

#[cfg(feature = "python")]
impl pyo3::IntoPy<PyObject> for Object {
    fn into_py(self, py: Python<'_>) -> PyObject {
        match &self.0 {
            ObjV::Int(x) => x.into_py(py),
            ObjV::Float(x) => x.into_py(py),
            ObjV::Str(x) => x.as_str().into_py(py),
            ObjV::Boolean(x) => x.into_py(py),
            ObjV::List(x) => {
                PyList::new(py, x.borrow().iter().map(|x| x.clone().into_py(py))).into()
            }
            ObjV::Map(x) => {
                let r = PyDict::new(py);
                for (k, v) in x.borrow().iter() {
                    r.set_item(k.as_str(), v.clone().into_py(py)).unwrap();
                }
                r.into()
            }
            ObjV::Null => (None as Option<bool>).into_py(py),
            ObjV::ListIter(_, _) => 1.into_py(py), // TODO
            ObjV::Func(x) => x.into_py(py),
        }
    }
}

#[cfg(test)]
mod test {
    use core::cmp::Ordering;

    use crate::formatting::{
        AlignSpec, FloatFormatType, FormatSpec, FormatType, GroupingSpec, IntegerFormatType, SignSpec,
        UppercaseSpec,
    };

    use super::Object;

    #[test]
    fn to_string() {
        assert_eq!(Object::new_int(1).to_string(), "1");
        assert_eq!(Object::new_int(-1).to_string(), "-1");
        assert_eq!(
            Object::new_int_from_str("9223372036854775808").unwrap().to_string(),
            "9223372036854775808"
        );

        assert_eq!(Object::float(1.2).to_string(), "1.2");
        assert_eq!(Object::float(1.0).to_string(), "1");

        assert_eq!(Object::float(-1.2).to_string(), "-1.2");
        assert_eq!(Object::float(-1.0).to_string(), "-1");

        assert_eq!(Object::bool(true).to_string(), "true");
        assert_eq!(Object::bool(false).to_string(), "false");
        assert_eq!(Object::null().to_string(), "null");

        assert_eq!(Object::new_str("alpha").to_string(), "\"alpha\"");
        assert_eq!(Object::new_str("\"alpha\\").to_string(), "\"\\\"alpha\\\\\"");

        assert_eq!(Object::new_list().to_string(), "[]");
        assert_eq!(
            Object::from(vec![Object::new_int(1), Object::new_str("alpha")]).to_string(),
            "[1, \"alpha\"]"
        );

        assert_eq!(Object::new_map().to_string(), "{}");
        assert_eq!(
            Object::from(vec![("a", Object::new_int(1)),]).to_string(),
            "{a: 1}"
        );
    }

    #[test]
    fn format() {
        assert_eq!(
            Object::new_str("alpha").format(&Default::default()),
            Ok("alpha".to_string())
        );
        assert_eq!(
            Object::new_str("\"alpha\"").format(&Default::default()),
            Ok("\"alpha\"".to_string())
        );
        assert_eq!(
            Object::new_str("\"al\\pha\"").format(&Default::default()),
            Ok("\"al\\pha\"".to_string())
        );
        assert_eq!(
            Object::bool(true).format(&Default::default()),
            Ok("true".to_string())
        );
        assert_eq!(
            Object::bool(false).format(&Default::default()),
            Ok("false".to_string())
        );
        assert_eq!(
            Object::null().format(&Default::default()),
            Ok("null".to_string())
        );
        assert_eq!(
            Object::new_int(0).format(&Default::default()),
            Ok("0".to_string())
        );
        assert_eq!(
            Object::new_int(-2).format(&Default::default()),
            Ok("-2".to_string())
        );
        assert_eq!(
            Object::new_int(5).format(&Default::default()),
            Ok("5".to_string())
        );

        assert_eq!(
            Object::new_str("dong").format(&FormatSpec {
                fill: ' ',
                width: Some(10),
                ..Default::default()
            }),
            Ok("dong      ".to_string()),
        );

        assert_eq!(
            Object::new_str("dong").format(&FormatSpec {
                fill: ' ',
                width: Some(2),
                ..Default::default()
            }),
            Ok("dong".to_string()),
        );

        assert_eq!(
            Object::new_str("dong").format(&FormatSpec {
                fill: ' ',
                width: Some(12),
                align: Some(AlignSpec::left()),
                ..Default::default()
            }),
            Ok("dong        ".to_string()),
        );

        assert_eq!(
            Object::new_str("dong").format(&FormatSpec {
                fill: ' ',
                width: Some(8),
                align: Some(AlignSpec::right()),
                ..Default::default()
            }),
            Ok("    dong".to_string()),
        );

        assert_eq!(
            Object::new_str("dong").format(&FormatSpec {
                fill: ' ',
                width: Some(8),
                align: Some(AlignSpec::center()),
                ..Default::default()
            }),
            Ok("  dong  ".to_string()),
        );

        assert_eq!(
            Object::new_str("dong").format(&FormatSpec {
                fill: ' ',
                width: Some(7),
                align: Some(AlignSpec::center()),
                ..Default::default()
            }),
            Ok(" dong  ".to_string()),
        );

        assert_eq!(
            Object::new_str("dong").format(&FormatSpec {
                fill: '~',
                width: Some(8),
                align: Some(AlignSpec::center()),
                ..Default::default()
            }),
            Ok("~~dong~~".to_string()),
        );

        assert_eq!(
            Object::bool(true).format(&FormatSpec {
                fill: '~',
                width: Some(8),
                align: Some(AlignSpec::center()),
                ..Default::default()
            }),
            Ok("~~true~~".to_string()),
        );

        assert_eq!(
            Object::bool(false).format(&FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Decimal)),
                ..Default::default()
            }),
            Ok("0".to_string()),
        );

        assert_eq!(
            Object::bool(true).format(&FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Decimal)),
                ..Default::default()
            }),
            Ok("1".to_string()),
        );

        assert_eq!(
            Object::bool(false).format(&FormatSpec {
                fill: ' ',
                width: Some(6),
                align: Some(AlignSpec::right()),
                ..Default::default()
            }),
            Ok(" false".to_string()),
        );

        assert_eq!(
            Object::null().format(&FormatSpec {
                fill: ' ',
                width: Some(6),
                align: Some(AlignSpec::center()),
                ..Default::default()
            }),
            Ok(" null ".to_string()),
        );

        assert_eq!(
            Object::new_int(0).format(&FormatSpec {
                sign: Some(SignSpec::Plus),
                ..Default::default()
            }),
            Ok("+0".to_string()),
        );

        assert_eq!(
            Object::new_int(15).format(&FormatSpec {
                sign: Some(SignSpec::Space),
                ..Default::default()
            }),
            Ok(" 15".to_string()),
        );

        assert_eq!(
            Object::new_int(11).format(&FormatSpec {
                sign: Some(SignSpec::Minus),
                ..Default::default()
            }),
            Ok("11".to_string()),
        );

        assert_eq!(
            Object::new_int(-1).format(&FormatSpec {
                sign: Some(SignSpec::Plus),
                ..Default::default()
            }),
            Ok("-1".to_string()),
        );

        assert_eq!(
            Object::new_int(-13).format(&FormatSpec {
                sign: Some(SignSpec::Space),
                ..Default::default()
            }),
            Ok("-13".to_string()),
        );

        assert_eq!(
            Object::new_int(-10).format(&FormatSpec {
                sign: Some(SignSpec::Minus),
                ..Default::default()
            }),
            Ok("-10".to_string()),
        );

        assert_eq!(
            Object::new_int(15).format(&FormatSpec {
                align: Some(AlignSpec::left()),
                width: Some(10),
                ..Default::default()
            }),
            Ok("15        ".to_string()),
        );

        assert_eq!(
            Object::new_int(15).format(&FormatSpec {
                align: Some(AlignSpec::center()),
                width: Some(10),
                ..Default::default()
            }),
            Ok("    15    ".to_string()),
        );

        assert_eq!(
            Object::new_int(15).format(&FormatSpec {
                align: Some(AlignSpec::right()),
                width: Some(10),
                ..Default::default()
            }),
            Ok("        15".to_string()),
        );

        assert_eq!(
            Object::new_int(-15).format(&FormatSpec {
                align: Some(AlignSpec::left()),
                width: Some(10),
                ..Default::default()
            }),
            Ok("-15       ".to_string()),
        );

        assert_eq!(
            Object::new_int(-15).format(&FormatSpec {
                align: Some(AlignSpec::center()),
                width: Some(10),
                ..Default::default()
            }),
            Ok("   -15    ".to_string()),
        );

        assert_eq!(
            Object::new_int(-15).format(&FormatSpec {
                align: Some(AlignSpec::right()),
                width: Some(10),
                ..Default::default()
            }),
            Ok("       -15".to_string()),
        );

        assert_eq!(
            Object::new_int(-15).format(&FormatSpec {
                align: Some(AlignSpec::AfterSign),
                width: Some(10),
                ..Default::default()
            }),
            Ok("-       15".to_string()),
        );

        assert_eq!(
            Object::new_int(15).format(&FormatSpec {
                align: Some(AlignSpec::AfterSign),
                width: Some(10),
                ..Default::default()
            }),
            Ok("        15".to_string()),
        );

        assert_eq!(
            Object::new_int(23).format(&FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Decimal)),
                ..Default::default()
            }),
            Ok("23".to_string()),
        );

        assert_eq!(
            Object::new_int(23).format(&FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Binary)),
                ..Default::default()
            }),
            Ok("10111".to_string()),
        );

        assert_eq!(
            Object::new_int(23).format(&FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Octal)),
                ..Default::default()
            }),
            Ok("27".to_string()),
        );

        assert_eq!(
            Object::new_int(42).format(&FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(
                    UppercaseSpec::Lower
                ))),
                ..Default::default()
            }),
            Ok("2a".to_string()),
        );

        assert_eq!(
            Object::new_int(42).format(&FormatSpec {
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(
                    UppercaseSpec::Upper
                ))),
                ..Default::default()
            }),
            Ok("2A".to_string()),
        );

        assert_eq!(
            Object::new_int(23).format(&FormatSpec {
                alternate: true,
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Decimal)),
                ..Default::default()
            }),
            Ok("23".to_string()),
        );

        assert_eq!(
            Object::new_int(23).format(&FormatSpec {
                alternate: true,
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Binary)),
                ..Default::default()
            }),
            Ok("0b10111".to_string()),
        );

        assert_eq!(
            Object::new_int(23).format(&FormatSpec {
                alternate: true,
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Octal)),
                ..Default::default()
            }),
            Ok("0o27".to_string()),
        );

        assert_eq!(
            Object::new_int(42).format(&FormatSpec {
                alternate: true,
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(
                    UppercaseSpec::Lower
                ))),
                ..Default::default()
            }),
            Ok("0x2a".to_string()),
        );

        assert_eq!(
            Object::new_int(42).format(&FormatSpec {
                alternate: true,
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(
                    UppercaseSpec::Upper
                ))),
                ..Default::default()
            }),
            Ok("0X2A".to_string()),
        );

        assert_eq!(
            Object::new_int(12738912).format(&FormatSpec {
                grouping: Some(GroupingSpec::Comma),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Decimal)),
                ..Default::default()
            }),
            Ok("12,738,912".to_string()),
        );

        assert_eq!(
            Object::new_int(12738912).format(&FormatSpec {
                grouping: Some(GroupingSpec::Underscore),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Binary)),
                ..Default::default()
            }),
            Ok("1100_0010_0110_0001_0110_0000".to_string()),
        );

        assert_eq!(
            Object::new_int(12738912).format(&FormatSpec {
                grouping: Some(GroupingSpec::Underscore),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Octal)),
                ..Default::default()
            }),
            Ok("6046_0540".to_string()),
        );

        assert_eq!(
            Object::new_int(12738912).format(&FormatSpec {
                grouping: Some(GroupingSpec::Comma),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(
                    UppercaseSpec::Lower
                ))),
                ..Default::default()
            }),
            Ok("c2,6160".to_string()),
        );

        assert_eq!(
            Object::new_int(12738912).format(&FormatSpec {
                width: Some(12),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(
                    UppercaseSpec::Lower
                ))),
                ..Default::default()
            }),
            Ok("      c26160".to_string()),
        );

        assert_eq!(
            Object::new_int(12738912).format(&FormatSpec {
                sign: Some(SignSpec::Plus),
                width: Some(12),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(
                    UppercaseSpec::Lower
                ))),
                ..Default::default()
            }),
            Ok("     +c26160".to_string()),
        );

        assert_eq!(
            Object::new_int(12738912).format(&FormatSpec {
                align: Some(AlignSpec::AfterSign),
                sign: Some(SignSpec::Plus),
                width: Some(12),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(
                    UppercaseSpec::Lower
                ))),
                ..Default::default()
            }),
            Ok("+     c26160".to_string()),
        );

        assert_eq!(
            Object::new_int(12738912).format(&FormatSpec {
                align: Some(AlignSpec::AfterSign),
                sign: Some(SignSpec::Plus),
                alternate: true,
                width: Some(12),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(
                    UppercaseSpec::Lower
                ))),
                ..Default::default()
            }),
            Ok("+0x   c26160".to_string()),
        );

        assert_eq!(
            Object::new_int(12738912).format(&FormatSpec {
                align: Some(AlignSpec::AfterSign),
                sign: Some(SignSpec::Plus),
                alternate: true,
                width: Some(12),
                grouping: Some(GroupingSpec::Underscore),
                fmt_type: Some(FormatType::Integer(IntegerFormatType::Hex(
                    UppercaseSpec::Lower
                ))),
                ..Default::default()
            }),
            Ok("+0x  c2_6160".to_string()),
        );

        assert_eq!(
            Object::float(1.234).format(&FormatSpec {
                precision: Some(1),
                ..Default::default()
            }),
            Ok("1.2".to_string()),
        );

        assert_eq!(
            Object::float(1.234).format(&FormatSpec {
                precision: Some(6),
                ..Default::default()
            }),
            Ok("1.234000".to_string()),
        );

        assert_eq!(
            Object::float(1.234).format(&FormatSpec {
                fmt_type: Some(FormatType::Float(FloatFormatType::Fixed)),
                ..Default::default()
            }),
            Ok("1.234000".to_string()),
        );

        assert_eq!(
            Object::float(1.234).format(&FormatSpec {
                precision: Some(9),
                fmt_type: Some(FormatType::Float(FloatFormatType::Fixed)),
                ..Default::default()
            }),
            Ok("1.234000000".to_string()),
        );

        assert_eq!(
            Object::float(12.34).format(&FormatSpec {
                precision: Some(5),
                fmt_type: Some(FormatType::Float(FloatFormatType::Sci(
                    UppercaseSpec::Lower
                ))),
                ..Default::default()
            }),
            Ok("1.23400e1".to_string()),
        );

        assert_eq!(
            Object::float(12.34).format(&FormatSpec {
                fmt_type: Some(FormatType::Float(FloatFormatType::Sci(
                    UppercaseSpec::Upper
                ))),
                ..Default::default()
            }),
            Ok("1.234000E1".to_string()),
        );

        assert_eq!(
            Object::float(12.34).format(&FormatSpec {
                fmt_type: Some(FormatType::Float(FloatFormatType::General)),
                ..Default::default()
            }),
            Ok("12.34".to_string()),
        );

        assert_eq!(
            Object::float(12.34).format(&FormatSpec {
                align: Some(AlignSpec::AfterSign),
                width: Some(8),
                ..Default::default()
            }),
            Ok("   12.34".to_string()),
        );

        assert_eq!(
            Object::float(-12.34).format(&FormatSpec {
                align: Some(AlignSpec::AfterSign),
                width: Some(8),
                ..Default::default()
            }),
            Ok("-  12.34".to_string()),
        );

        assert_eq!(
            Object::float(12.34).format(&FormatSpec {
                align: Some(AlignSpec::AfterSign),
                sign: Some(SignSpec::Plus),
                width: Some(8),
                ..Default::default()
            }),
            Ok("+  12.34".to_string()),
        );

        assert_eq!(
            Object::float(12.34).format(&FormatSpec {
                align: Some(AlignSpec::left()),
                sign: Some(SignSpec::Plus),
                width: Some(8),
                ..Default::default()
            }),
            Ok("+12.34  ".to_string()),
        );

        assert_eq!(
            Object::float(12.34).format(&FormatSpec {
                align: Some(AlignSpec::center()),
                sign: Some(SignSpec::Plus),
                width: Some(8),
                ..Default::default()
            }),
            Ok(" +12.34 ".to_string()),
        );

        assert_eq!(
            Object::float(1000000.0).format(&FormatSpec {
                grouping: Some(GroupingSpec::Underscore),
                ..Default::default()
            }),
            Ok("1_000_000".to_string()),
        );

        assert_eq!(
            Object::float(1000000.0).format(&FormatSpec {
                grouping: Some(GroupingSpec::Underscore),
                precision: Some(8),
                ..Default::default()
            }),
            Ok("1_000_000.00000000".to_string()),
        );
    }

    #[test]
    fn compare() {
        assert_eq!(
            Object::float(0.1).partial_cmp(&Object::new_int_from_str("0").unwrap()),
            Some(Ordering::Greater)
        );
        assert_eq!(
            Object::float(0.5).partial_cmp(&Object::new_int_from_str("0").unwrap()),
            Some(Ordering::Greater)
        );
        assert_eq!(
            Object::float(0.9).partial_cmp(&Object::new_int_from_str("0").unwrap()),
            Some(Ordering::Greater)
        );
        assert_eq!(
            Object::float(1.0).partial_cmp(&Object::new_int_from_str("0").unwrap()),
            Some(Ordering::Greater)
        );
        assert_eq!(
            Object::float(0.0).partial_cmp(&Object::new_int_from_str("0").unwrap()),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Object::float(-0.0).partial_cmp(&Object::new_int_from_str("0").unwrap()),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Object::float(-0.1).partial_cmp(&Object::new_int_from_str("0").unwrap()),
            Some(Ordering::Less)
        );
        assert_eq!(
            Object::float(-0.5).partial_cmp(&Object::new_int_from_str("0").unwrap()),
            Some(Ordering::Less)
        );
        assert_eq!(
            Object::float(-0.9).partial_cmp(&Object::new_int_from_str("0").unwrap()),
            Some(Ordering::Less)
        );
        assert_eq!(
            Object::float(-1.0).partial_cmp(&Object::new_int_from_str("0").unwrap()),
            Some(Ordering::Less)
        );

        assert_eq!(
            Object::float(-1.0).partial_cmp(&Object::new_int_from_str("-1").unwrap()),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Object::float(-1.1).partial_cmp(&Object::new_int_from_str("-1").unwrap()),
            Some(Ordering::Less)
        );
        assert_eq!(
            Object::float(-0.9).partial_cmp(&Object::new_int_from_str("-1").unwrap()),
            Some(Ordering::Greater)
        );

        assert_eq!(
            Object::float(1.0).partial_cmp(&Object::new_int_from_str("1").unwrap()),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Object::float(1.1).partial_cmp(&Object::new_int_from_str("1").unwrap()),
            Some(Ordering::Greater)
        );
        assert_eq!(
            Object::float(0.9).partial_cmp(&Object::new_int_from_str("1").unwrap()),
            Some(Ordering::Less)
        );

        assert_eq!(
            Object::new_int_from_str("0")
                .unwrap()
                .partial_cmp(&Object::float(0.1)),
            Some(Ordering::Less)
        );
        assert_eq!(
            Object::new_int_from_str("0")
                .unwrap()
                .partial_cmp(&Object::float(0.5)),
            Some(Ordering::Less)
        );
        assert_eq!(
            Object::new_int_from_str("0")
                .unwrap()
                .partial_cmp(&Object::float(0.9)),
            Some(Ordering::Less)
        );
        assert_eq!(
            Object::new_int_from_str("0")
                .unwrap()
                .partial_cmp(&Object::float(1.0)),
            Some(Ordering::Less)
        );
        assert_eq!(
            Object::new_int_from_str("0")
                .unwrap()
                .partial_cmp(&Object::float(0.0)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Object::new_int_from_str("0")
                .unwrap()
                .partial_cmp(&Object::float(-0.0)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Object::new_int_from_str("0")
                .unwrap()
                .partial_cmp(&Object::float(-0.1)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            Object::new_int_from_str("0")
                .unwrap()
                .partial_cmp(&Object::float(-0.5)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            Object::new_int_from_str("0")
                .unwrap()
                .partial_cmp(&Object::float(-0.9)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            Object::new_int_from_str("0")
                .unwrap()
                .partial_cmp(&Object::float(-1.0)),
            Some(Ordering::Greater)
        );

        assert_eq!(
            Object::new_int_from_str("-1")
                .unwrap()
                .partial_cmp(&Object::float(-1.0)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Object::new_int_from_str("-1")
                .unwrap()
                .partial_cmp(&Object::float(-1.1)),
            Some(Ordering::Greater)
        );
        assert_eq!(
            Object::new_int_from_str("-1")
                .unwrap()
                .partial_cmp(&Object::float(-0.9)),
            Some(Ordering::Less)
        );

        assert_eq!(
            Object::new_int_from_str("1")
                .unwrap()
                .partial_cmp(&Object::float(1.0)),
            Some(Ordering::Equal)
        );
        assert_eq!(
            Object::new_int_from_str("1")
                .unwrap()
                .partial_cmp(&Object::float(1.1)),
            Some(Ordering::Less)
        );
        assert_eq!(
            Object::new_int_from_str("1")
                .unwrap()
                .partial_cmp(&Object::float(0.9)),
            Some(Ordering::Greater)
        );
    }
}

#[cfg(test)]
mod test_serialization {
    use super::Object;

    fn check(x: Object) {
        assert_eq!(
            x.serialize()
                .map(|y| Object::deserialize(&y))
                .flatten()
                .map(|x| x.0),
            Some(x)
        )
    }

    #[test]
    fn nulls() {
        check(Object::null());
    }

    #[test]
    fn integers() {
        check(Object::new_int(1));
        check(Object::new_int(9223372036854775807_i64));
        check(Object::new_int(-9223372036854775807_i64));
        check(Object::new_int_from_str("9223372036854775808").unwrap());
    }

    #[test]
    fn strings() {
        check(Object::new_str(""));
        check(Object::new_str("dingbob"));
        check(Object::new_str("ding\"bob"));
    }

    #[test]
    fn bools() {
        check(Object::bool(true));
        check(Object::bool(false));
    }

    #[test]
    fn floats() {
        check(Object::float(1.2234));
    }

    #[test]
    fn maps() {
        check(Object::from(vec![
            ("a", Object::new_int(1)),
            ("b", Object::bool(true)),
            ("c", Object::new_str("zomg")),
        ]));
    }

    #[test]
    fn lists() {
        check(Object::from(vec![
            Object::new_int(1),
            Object::new_str("dingbob"),
            Object::float(-2.11),
            Object::bool(false),
        ]));
    }
}
