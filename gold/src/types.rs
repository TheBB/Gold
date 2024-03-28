use std::fmt::{Debug, Display};
use std::hash::Hash;

use gc::custom_trace;
use indexmap::{map::Iter, IndexMap};
use serde::{Deserialize, Serialize, Serializer, Deserializer};
use serde::de::Visitor;
use symbol_table::GlobalSymbol;

use crate::{Error, Object};
use crate::builtins::BUILTINS;

pub use gc::Gc;

/// Type used for all interned strings, map keys, variable names, etc.
pub type Key = GlobalSymbol;

/// Type used for lists.
pub type List = Vec<Object>;

/// Type used for mapping of strings (that is, [`Key`]) to objects.
pub type Map = OrderedMap<Key, Object>;

pub type NativeFunction = fn(&List, Option<&Map>) -> Result<Object, Error>;

pub type NativeClosure = dyn Fn(&List, Option<&Map>) -> Result<Object, Error>;

pub type Cell = GcCell<Option<Object>>;

#[derive(Copy, Clone)]
pub struct Builtin {
    func: NativeFunction,
    name: Key,
}

impl Builtin {
    pub fn new(func: NativeFunction, name: Key) -> Builtin {
        Builtin { func, name }
    }

    pub fn call(&self, args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
        (self.func)(args, kwargs)
    }

    pub fn name(&self) -> Key {
        self.name
    }

    pub fn native_callable(&self) -> &NativeFunction {
        &self.func
    }
}

impl Debug for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Builtin").field("name", &self.name).finish()
    }
}

// Custom serialization and deserialization logic.
impl Serialize for Builtin {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.name.as_str())
    }
}
struct BuiltinVisitor;

impl<'a> Visitor<'a> for BuiltinVisitor {
    type Value = Builtin;

    fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
        formatter.write_str("a string")
    }

    fn visit_str<E: serde::de::Error>(self, v: &str) -> Result<Self::Value, E> {
        BUILTINS
            .0
            .get(v)
            .map(|i| BUILTINS.1[*i])
            .ok_or(E::custom("unknown builtin name"))
    }
}

impl<'a> Deserialize<'a> for Builtin {
    fn deserialize<D: Deserializer<'a>>(deserializer: D) -> Result<Self, D::Error> where {
        deserializer.deserialize_str(BuiltinVisitor)
    }
}


/// Enumeration of all the different types a Gold object can have.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum Type {
    /// IntVariant
    Integer,

    /// f64
    Float,

    /// StrVariant
    String,

    /// bool
    Boolean,

    /// Vec<Object>
    List,

    /// IndexMap<Key, Object>
    Map,

    /// FuncVariant
    Function,

    /// Iterator
    Iterator,

    /// The empty variant
    Null,
}

// It's desirable that these names correspond to the built-in conversion
// functions. When Gold gets proper support for types, this source of ambiguity
// will be rectified.
impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer => f.write_str("int"),
            Self::Float => f.write_str("float"),
            Self::String => f.write_str("str"),
            Self::Boolean => f.write_str("bool"),
            Self::List => f.write_str("list"),
            Self::Map => f.write_str("map"),
            Self::Function => f.write_str("function"),
            Self::Iterator => f.write_str("iterator"),
            Self::Null => f.write_str("null"),
        }
    }
}

#[derive(Clone, gc::Trace, gc::Finalize, Debug, PartialEq)]
pub struct GcCell<T: ?Sized + 'static>(gc::Gc<gc::GcCell<T>>);

impl<T: gc::Trace> GcCell<T> {
    pub fn new(obj: T) -> GcCell<T> {
        GcCell(gc::Gc::new(gc::GcCell::new(obj)))
    }

    pub fn borrow(&self) -> gc::GcCellRef<'_, T> {
        self.0.borrow()
    }
}

impl<T: gc::Trace> GcCell<T> {
    pub fn borrow_mut(&self) -> gc::GcCellRefMut<'_, T> {
        self.0.borrow_mut()
    }
}

impl<T: gc::Trace + Serialize> Serialize for GcCell<T> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.borrow().serialize(serializer)
    }
}

impl<'a, T: gc::Trace + Deserialize<'a>> Deserialize<'a> for GcCell<T> {
    fn deserialize<D: Deserializer<'a>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(GcCell::new(T::deserialize(deserializer)?))
    }
}

#[derive(Clone, Debug)]
pub struct OrderedMap<K, V>(IndexMap<K, V>);

impl<K, V> OrderedMap<K, V> {
    pub fn new() -> Self {
        Self(IndexMap::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> Iter<'_, K, V> {
        self.0.iter()
    }
}

impl<K: Hash + Eq, V> OrderedMap<K, V> {
    pub fn get(&self, k: &K) -> Option<&V> {
        self.0.get(k)
    }

    pub fn remove(&mut self, k: &K) -> Option<V> {
        self.0.remove(k)
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.0.insert(key, value)
    }
}

impl<K: Hash + Eq, V2, V1: PartialEq<V2>> PartialEq<OrderedMap<K, V2>> for OrderedMap<K, V1> {
    fn eq(&self, other: &OrderedMap<K, V2>) -> bool {
        self.0.eq(&other.0)
    }
}

impl<K: Serialize + Hash + Eq, V: Serialize> Serialize for OrderedMap<K, V> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

impl<'a, K: Deserialize<'a> + Eq + Hash, V: Deserialize<'a>> Deserialize<'a> for OrderedMap<K, V> {
    fn deserialize<D: Deserializer<'a>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(Self(IndexMap::deserialize(deserializer)?))
    }
}

impl<K: Copy, V: gc::Finalize> gc::Finalize for OrderedMap<K, V> {
    fn finalize(&self) {
        for (_, v) in self {
            v.finalize();
        }
    }
}

unsafe impl<K: Copy, V: gc::Trace> gc::Trace for OrderedMap<K, V> {
    custom_trace!(this, {
        for (_, v) in this {
            mark(v);
        }
    });
}

impl<'a, K, V> IntoIterator for &'a OrderedMap<K, V> {
    type Item = <&'a IndexMap<K, V> as IntoIterator>::Item;
    type IntoIter = <&'a IndexMap<K, V> as IntoIterator>::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        (&self.0).into_iter()
    }
}

impl<K: Hash + Eq, V> FromIterator<(K, V)> for OrderedMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        OrderedMap(IndexMap::from_iter(iter))
    }
}

/// Enumerates all the unary operators in the Gold language.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum UnOp {
    /// Passthrough (do-nothing) operator, e.g. the unary plus
    Passthrough,

    /// Arithmetical negation (unary minus)
    ArithmeticalNegate,

    /// Logical negation (unary 'not')
    LogicalNegate,
}

/// Enumerates all the binary operators in the Gold language.
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub enum BinOp {
    /// Index or subscripting operator
    Index,

    /// Exponentiation
    Power,

    /// Multiplication
    Multiply,

    /// Integer division
    IntegerDivide,

    /// Mathematical division
    Divide,

    /// Addition
    Add,

    /// Subtraction
    Subtract,

    /// Less-than
    Less,

    /// Greater-than
    Greater,

    /// Less-than-or-equal-to
    LessEqual,

    /// Greater-than-or-equal-to
    GreaterEqual,

    /// Equality
    Equal,

    /// Inequality
    NotEqual,

    /// Containment
    Contains,

    /// Logical conjunction
    And,

    /// Logical disjunction
    Or,
}
