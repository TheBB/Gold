//! Function implementation.

use std::fmt::Debug;
use std::rc::Rc;

use gc::{Finalize, Gc, Trace};
use serde::{Deserialize, Serialize};

#[cfg(feature = "python")]
use pyo3::FromPyObject;

#[cfg(feature = "python")]
use pyo3::{Py, PyAny, Python, pymethods, pyclass, PyObject, IntoPy};

#[cfg(feature = "python")]
use pyo3::types::{PyTuple, PyDict};

#[cfg(feature = "python")]
use pyo3::exceptions::PyTypeError;

use super::{List, Map, Object};
use crate::compile::CompiledFunction;
use crate::error::{Error, Reason};
use crate::eval::Vm;
use crate::types::{Builtin, Cell, GcCell, NativeClosure};
use crate::ImportConfig;

#[derive(Clone, Serialize, Deserialize, Trace, Finalize)]
enum FuncV {
    Closure(Gc<CompiledFunction>, GcCell<Vec<Cell>>),
    Builtin(#[unsafe_ignore_trace] Builtin),

    #[serde(skip)]
    NativeClosure(#[unsafe_ignore_trace] Rc<NativeClosure>),
}

impl Debug for FuncV {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Closure(x, e) => f
                .debug_tuple("Func::Closure")
                .field(x)
                .field(e)
                .finish(),
            Self::Builtin(b) => f.debug_tuple("Func::Builtin").field(b).finish(),
            Self::NativeClosure(_) => f.debug_tuple("Func::NativeClosure").finish(),
        }
    }
}

/// The function variant represents all possible forms of callable objects in
/// Gold.
#[derive(Clone, Debug, Serialize, Deserialize, Trace, Finalize)]
pub struct Func(FuncV);

impl From<Builtin> for Func {
    fn from(value: Builtin) -> Self {
        Self(FuncV::Builtin(value))
    }
}

impl From<Rc<NativeClosure>> for Func {
    fn from(value: Rc<NativeClosure>) -> Self {
        Self(FuncV::NativeClosure(value))
    }
}

impl From<CompiledFunction> for Func {
    fn from(value: CompiledFunction) -> Self {
        Self(FuncV::Closure(Gc::new(value), GcCell::new(vec![])))
    }
}

impl Func {
    /// All functions in Gold compare different to each other except built-ins.
    pub fn user_eq(&self, other: &Func) -> bool {
        let Self(this) = self;
        let Self(that) = other;
        match (this, that) {
            (FuncV::Builtin(x), FuncV::Builtin(y)) => x.name() == y.name(),
            _ => false,
        }
    }

    /// The function call operator.
    pub fn call(&self, args: &List, kwargs: Option<&Map>) -> Result<Object, Error> {
        let Self(this) = self;
        match this {
            FuncV::NativeClosure(f) => f(args, kwargs),
            FuncV::Builtin(f) => f.call(args, kwargs),
            FuncV::Closure(f, e) => {
                let importer = ImportConfig::default();
                let mut vm = Vm::new(&importer);
                vm.eval_with_args(f.as_ref().clone(), e.clone(), args, kwargs)
            }
        }
    }

    pub fn push_cell(&self, other: Cell) -> Result<(), Error> {
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

    pub fn native_callable(&self) -> Option<&NativeClosure> {
        let Self(this) = self;
        match this {
            FuncV::NativeClosure(closure) => Some(closure.as_ref()),
            FuncV::Builtin(builtin) => Some(builtin.native_callable()),
            _ => None,
        }
    }

    pub fn get_closure(&self) -> Option<(Gc<CompiledFunction>, GcCell<Vec<Cell>>)> {
        let Self(this) = self;
        match this {
            FuncV::Closure(f, e) => Some((f.clone(), e.clone())),
            _ => None,
        }
    }
}

#[cfg(feature = "python")]
#[pyclass(unsendable)]
#[derive(Clone)]
struct PyFunction(Func);

#[cfg(feature = "python")]
#[pymethods]
impl PyFunction {
    #[args(args = "*", kwargs = "**")]
    fn __call__(
        &self,
        py: Python<'_>,
        args: &PyTuple,
        kwargs: Option<&PyDict>,
    ) -> pyo3::PyResult<Py<PyAny>> {
        let func = Object::new_func(self.0.clone());

        let posargs_obj = args.extract::<Object>()?;
        let posargs = posargs_obj.get_list().ok_or_else(|| {
            pyo3::exceptions::PyTypeError::new_err(
                "internal error py001 - this should not happen, please file a bug report",
            )
        })?;

        // Extract keyword arguments
        let kwargs_obj = kwargs.map(|x| x.extract::<Object>()).transpose()?;
        let result = if let Some(x) = kwargs_obj {
            let gkwargs = x.get_map().ok_or_else(|| {
                pyo3::exceptions::PyTypeError::new_err(
                    "internal error py002 - this should not happen, please file a bug report",
                )
            })?;
            func.call(&*posargs, Some(&*gkwargs))
        } else {
            func.call(&*posargs, None)
        }
        .map_err(Error::to_py)?;

        Ok(result.into_py(py))
    }
}

#[cfg(feature = "python")]
impl IntoPy<PyObject> for &Func {
    fn into_py(self, py: Python<'_>) -> PyObject {
        PyFunction(self.clone()).into_py(py)
    }
}

#[cfg(feature = "python")]
impl<'s> FromPyObject<'s> for Func {
    fn extract(obj: &'s PyAny) -> pyo3::prelude::PyResult<Self> {
        if let Ok(PyFunction(x)) = obj.extract::<PyFunction>() {
            Ok(x)
        } else {
            Err(PyTypeError::new_err(format!(
                "uncovertible type: {}",
                obj.get_type().name().unwrap_or("unknown")
            )))
        }
    }
}
