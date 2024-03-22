//! Function implementation.

use std::fmt::Debug;
use std::rc::Rc;

use gc::{Finalize, Gc, Trace};
use serde::de::Visitor;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::{Key, List, Map, Object};
use crate::builtins::BUILTINS;
use crate::compile::Function;
use crate::error::Error;
use crate::eval::Vm;
use crate::wrappers::GcCell;
use crate::ImportConfig;

/// A builtin function is a 'pure' function implemented in Rust associated with
/// a name. The name is used for serializing. When deserializing, the name is
/// looked up in the  mapping.
#[derive(Copy, Clone)]
pub(crate) struct Builtin {
    /// The rust callable for evaluating the function.
    pub func: fn(&List, Option<&Map>) -> Result<Object, Error>,

    /// The name of the function.
    pub name: Key,
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

/// A 'pure' function implemented in Rust. Unlike [`Builtin`], this form of
/// function is backed by a dynamic callable object, which can be anything, such
/// as a closure. Such objects can be created dynamically, and are thus
/// necessary for implementing Gold-callable functions in other languages like
/// Python. This also makes them inherently non-serializable.
#[derive(Clone)]
pub(crate) struct Closure(pub(crate) Rc<dyn Fn(&List, Option<&Map>) -> Result<Object, Error>>);

/// The function variant represents all possible forms of callable objects in
/// Gold.
#[derive(Clone, Serialize, Deserialize, Trace, Finalize)]
pub(crate) enum FuncVariant {
    /// Function implemented in Gold.
    Func(Gc<Function>, Gc<GcCell<Vec<Gc<GcCell<Object>>>>>),

    /// Static (serializable) function implemented in Rust.
    Builtin(#[unsafe_ignore_trace] Builtin),

    /// Dynamic (unserializable) function implemented in Rust.
    #[serde(skip)]
    Closure(#[unsafe_ignore_trace] Closure),
}

impl Debug for FuncVariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Func(x, e) => f
                .debug_tuple("FuncVariant::Func")
                .field(x)
                .field(e)
                .finish(),
            Self::Builtin(_) => f.debug_tuple("FuncVariant::Builtin").finish(),
            Self::Closure(_) => f.debug_tuple("FuncVariant::Closure").finish(),
        }
    }
}

impl From<Builtin> for FuncVariant {
    fn from(value: Builtin) -> Self {
        FuncVariant::Builtin(value)
    }
}

impl From<Closure> for FuncVariant {
    fn from(value: Closure) -> Self {
        FuncVariant::Closure(value)
    }
}

impl FuncVariant {
    /// All functions in Gold compare different to each other except built-ins.
    pub fn user_eq(&self, other: &FuncVariant) -> bool {
        match (self, other) {
            (FuncVariant::Builtin(x), FuncVariant::Builtin(y)) => x.name == y.name,
            _ => false,
        }
    }

    /// The function call operator.
    pub(crate) fn call(&self, args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
        match self {
            FuncVariant::Closure(Closure(f)) => f(args, kwargs),
            FuncVariant::Builtin(Builtin { func: f, .. }) => f(args, kwargs),
            FuncVariant::Func(f, e) => {
                let importer = ImportConfig::default();
                let mut vm = Vm::new(&importer);
                vm.eval_with_args(f.as_ref().clone(), e.clone(), args, kwargs)
            }
        }
    }
}
