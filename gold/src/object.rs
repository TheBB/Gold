//! A Gold object is represented by the [`Object`] type. Internally an Object
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

use gc::{Finalize, Gc, GcCellRef, GcCellRefMut, Trace};
use json::JsonValue;
use num_bigint::BigInt;
use rmp_serde::{decode, encode};
use serde::{Deserialize, Serialize};
use symbol_table::GlobalSymbol;

use crate::compile::Function;
use crate::traits::{ToMap, ToVec};

use crate::error::{Error, Internal, Reason, TypeMismatch, Value};
use crate::formatting::FormatSpec;
use crate::wrappers::GcCell;
use crate::{ast, Key, List, Map, Type};

use function::FuncVariant;
use integer::IntVariant;
use string::StrVariant;

/// The current serialization format version.
const SERIALIZE_VERSION: i32 = 1;

// Object variant
// ------------------------------------------------------------------------------------------------

/// The object variant implements all possible variants of Gold objects,
/// although it's not the user-facing type, which is [`Object`], an opaque
/// struct enclosing an `ObjectVariant`.
#[derive(Clone, Debug, Serialize, Deserialize, Trace, Finalize)]
pub(crate) enum ObjV {
    /// Integers
    Int(IntVariant),

    /// Floating-point numbers
    Float(f64),

    /// Strings
    Str(StrVariant),

    /// Booleans
    Boolean(bool),

    /// Lists
    List(Gc<GcCell<List>>),

    /// Mappings
    Map(Gc<GcCell<Map>>),

    /// Functions
    Func(FuncVariant),

    /// Iterator
    ListIter(Gc<GcCell<usize>>, Gc<GcCell<List>>),

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

// Object
// ------------------------------------------------------------------------------------------------

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
    /// Mathematical negation.
    pub fn neg(&self) -> Result<Self, Error> {
        let Self(this) = self;
        match this {
            ObjV::Int(x) => Ok(Self(ObjV::Int(x.neg()))),
            ObjV::Float(x) => Ok(Self(ObjV::Float(-x))),
            _ => Err(Error::new(TypeMismatch::UnOp(
                self.type_of(),
                ast::UnOp::ArithmeticalNegate,
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
                    int_spec.format(&IntVariant::Small(i))
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

    /// Construct an interned string.
    pub fn str_interned(val: impl AsRef<str>) -> Self {
        Self(ObjV::Str(StrVariant::interned(val)))
    }

    /// Construct a non-interned string.
    pub fn str_natural(val: impl AsRef<str>) -> Self {
        Self(ObjV::Str(StrVariant::natural(val)))
    }

    /// Construct a string, deciding based on length whether to intern or not.
    pub fn str(val: impl AsRef<str>) -> Self {
        if val.as_ref().len() < 20 {
            Self::str_interned(val)
        } else {
            Self::str_natural(val)
        }
    }

    pub(crate) fn closure(val: Function) -> Self {
        Self(ObjV::Func(FuncVariant::Func(
            Gc::new(val),
            Gc::new(GcCell::new(vec![])),
        )))
    }

    /// Construct a string directly from an interned symbol.
    pub fn key(val: Key) -> Self {
        Self(ObjV::Str(StrVariant::Interned(val)))
    }

    /// Construct an integer.
    pub(crate) fn int<T>(val: T) -> Self
    where
        IntVariant: From<T>,
    {
        Self(ObjV::Int(IntVariant::from(val)))
    }

    /// Construct a big integer from a decimal string representation.
    pub fn bigint(x: impl AsRef<str>) -> Option<Self> {
        BigInt::from_str(x.as_ref())
            .ok()
            .map(|x| Self::from(x).numeric_normalize())
    }

    /// Normalize an integer variant, converting bignums to machine integers if
    /// they fit.
    pub fn numeric_normalize(&self) -> Self {
        let Self(this) = self;
        if let ObjV::Int(x) = this {
            Self(ObjV::Int(x.normalize()))
        } else {
            self.clone()
        }
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
        FuncVariant: From<T>,
    {
        Self(ObjV::Func(FuncVariant::from(val)))
    }

    /// Construct a list.
    pub fn list<T>(x: T) -> Self
    where
        T: ToVec<Object>,
    {
        Self(ObjV::List(Gc::new(GcCell::new(x.to_vec()))))
    }

    /// Construct an empty list.
    pub fn new_list() -> Self {
        Self(ObjV::List(Gc::new(GcCell::new(vec![]))))
    }

    /// Construct a map.
    pub(crate) fn map<T>(x: T) -> Self
    where
        T: ToMap<Key, Object>,
    {
        Self(ObjV::Map(Gc::new(GcCell::new(x.to_map()))))
    }


    /// Construct an empty map.
    pub fn new_map() -> Self {
        Self(ObjV::Map(Gc::new(GcCell::new(Map::new()))))
    }

    /// Construct an iterator
    pub fn iterator(obj: &Object) -> Result<Self, Error> {
        if let Object(ObjV::List(l)) = obj {
            Ok(Object(ObjV::ListIter(
                Gc::new(GcCell::new(0)),
                l.clone(),
            )))
        } else {
            Err(Error::new(TypeMismatch::Iterate(obj.type_of())))
        }
    }

    /// Get next value from an iterator
    pub fn next(&self) -> Result<Option<Self>, Error> {
        if let Object(ObjV::ListIter(index_cell, list)) = self {
            let mut index_cell_ref = index_cell.as_ref().borrow_mut();
            let l = list.as_ref().borrow();
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
    pub(crate) fn get_int(&self) -> Option<&IntVariant> {
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
    pub(crate) fn get_func_variant<'a>(&'a self) -> Option<&'a FuncVariant> {
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
    pub(crate) fn get_func(&self) -> Option<&FuncVariant> {
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

    /// The function call operator.
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
                ast::BinOp::Index,
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
            ast::BinOp::Contains,
        )))
    }

    pub(crate) fn push_to_list(&self, other: Object) -> Result<(), Error> {
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

    /// Wrap [`ObjectVariant::push_to_map`]
    pub(crate) fn push_to_map(&self, key: Self, value: Self) -> Result<(), Error> {
        self.push_to_map_key(
            key.get_key()
                .ok_or_else(|| Error::new(TypeMismatch::MapKey(key.type_of())))?,
            value,
        )
    }

    pub(crate) fn push_to_map_key(&self, key: Key, value: Object) -> Result<(), Error> {
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

    pub(crate) fn push_to_closure(&self, other: Gc<GcCell<Object>>) -> Result<(), Error> {
        let Self(this) = self;
        match this {
            ObjV::Func(FuncVariant::Func(_, enclosed)) => {
                let mut e = enclosed.borrow_mut();
                e.push(other);
                Ok(())
            }
            _ => Err(Error::new(Reason::None)),
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
        ixi: impl Fn(&IntVariant, &IntVariant) -> S,
        fxf: impl Fn(f64, f64) -> T,
        op: ast::BinOp,
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
            (ObjV::List(x), ObjV::List(y)) => Ok(Self::list(
                x.borrow()
                    .iter()
                    .chain(y.borrow().iter())
                    .map(Object::clone)
                    .collect::<List>(),
            )),
            (ObjV::Str(x), ObjV::Str(y)) => Ok(Self(ObjV::Str(x.add(y)))),
            _ => self.operate(other, IntVariant::add, |x, y| x + y, ast::BinOp::Add),
        }
    }

    /// The minus operator: mathematical subtraction.
    pub fn sub(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, IntVariant::sub, |x, y| x - y, ast::BinOp::Subtract)
    }

    /// The asterisk operator: mathematical multiplication.
    pub fn mul(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, IntVariant::mul, |x, y| x * y, ast::BinOp::Multiply)
    }

    /// The slash operator: mathematical division.
    pub fn div(&self, other: &Self) -> Result<Self, Error> {
        self.operate(other, IntVariant::div, |x, y| x / y, ast::BinOp::Divide)
    }

    /// The double slash operator: integer division.
    pub fn idiv(&self, other: &Self) -> Result<Self, Error> {
        self.operate(
            other,
            IntVariant::idiv,
            |x, y| (x / y).floor() as f64,
            ast::BinOp::IntegerDivide,
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
                    ast::BinOp::Power,
                ))
            })?;
        Ok(Self::from(xx.powf(yy)))
    }
}

impl FromIterator<Object> for Object {
    fn from_iter<T: IntoIterator<Item = Object>>(iter: T) -> Self {
        Object(ObjV::List(Gc::new(GcCell::new(
            iter.into_iter().collect(),
        ))))
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
        Object::str(value)
    }
}

impl From<Key> for Object {
    fn from(value: Key) -> Self {
        Object::key(value)
    }
}

impl<T> From<T> for Object
where
    IntVariant: From<T>,
{
    fn from(value: T) -> Self {
        Self(ObjV::Int(IntVariant::from(value)))
    }
}

impl From<f64> for Object {
    fn from(x: f64) -> Self {
        Self(ObjV::Float(x))
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
