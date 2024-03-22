//! Function implementation.

use std::fmt::Debug;
use std::rc::Rc;

use gc::{Finalize, Gc, Trace};
use serde::de::Visitor;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::{Key, List, Map, Object};
use crate::builtins::BUILTINS;
use crate::compile::Function;
use crate::error::{Error, Reason};
use crate::eval::Vm;
use crate::types::GcCell;
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
pub(crate) struct NativeClosure(pub(crate) Rc<dyn Fn(&List, Option<&Map>) -> Result<Object, Error>>);

#[derive(Clone, Serialize, Deserialize, Trace, Finalize)]
enum FuncV {
    Closure(Gc<Function>, GcCell<Vec<GcCell<Object>>>),
    Builtin(#[unsafe_ignore_trace] Builtin),

    #[serde(skip)]
    NativeClosure(#[unsafe_ignore_trace] NativeClosure),
}

impl Debug for FuncV {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Closure(x, e) => f
                .debug_tuple("Func::Closure")
                .field(x)
                .field(e)
                .finish(),
            Self::Builtin(b) => f.debug_tuple("Func::Builtin").field(&b.name).finish(),
            Self::NativeClosure(_) => f.debug_tuple("Func::NativeClosure").finish(),
        }
    }
}

/// The function variant represents all possible forms of callable objects in
/// Gold.
#[derive(Clone, Debug, Serialize, Deserialize, Trace, Finalize)]
pub(crate) struct Func(FuncV);

impl From<Builtin> for Func {
    fn from(value: Builtin) -> Self {
        Self(FuncV::Builtin(value))
    }
}

impl From<NativeClosure> for Func {
    fn from(value: NativeClosure) -> Self {
        Self(FuncV::NativeClosure(value))
    }
}

impl Func {
    pub fn closure(val: Function) -> Self {
        Self(FuncV::Closure(Gc::new(val), GcCell::new(vec![])))
    }

    /// All functions in Gold compare different to each other except built-ins.
    pub fn user_eq(&self, other: &Func) -> bool {
        let Self(this) = self;
        let Self(that) = other;
        match (this, that) {
            (FuncV::Builtin(x), FuncV::Builtin(y)) => x.name == y.name,
            _ => false,
        }
    }

    /// The function call operator.
    pub(crate) fn call(&self, args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
        let Self(this) = self;
        match this {
            FuncV::NativeClosure(NativeClosure(f)) => f(args, kwargs),
            FuncV::Builtin(Builtin { func: f, .. }) => f(args, kwargs),
            FuncV::Closure(f, e) => {
                let importer = ImportConfig::default();
                let mut vm = Vm::new(&importer);
                vm.eval_with_args(f.as_ref().clone(), e.clone(), args, kwargs)
            }
        }
    }

    pub(crate) fn push_to_closure(&self, other: GcCell<Object>) -> Result<(), Error> {
        let Self(this) = self;
        match this {
            FuncV::Closure(_, enclosed) => {
                let mut e = enclosed.borrow_mut();
                e.push(other);
                Ok(())
            }
            _ => Err(Error::new(Reason::None)),
        }
    }

    pub(crate) fn native_callable(&self) -> Option<&dyn Fn(&List, Option<&Map>) -> Result<Object, Error>> {
        let Self(this) = self;
        match this {
            FuncV::NativeClosure(closure) => Some(closure.0.as_ref()),
            FuncV::Builtin(Builtin { func, .. }) => Some(func),
            _ => None,
        }
    }

    pub(crate) fn get_closure(&self) -> Option<(Gc<Function>, GcCell<Vec<GcCell<Object>>>)> {
        let Self(this) = self;
        match this {
            FuncV::Closure(f, e) => Some((f.clone(), e.clone())),
            _ => None,
        }
    }
}
