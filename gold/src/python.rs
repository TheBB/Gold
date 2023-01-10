use std::collections::HashMap;
use std::sync::Arc;

use num_bigint::BigInt;

use pyo3::types::{PyList, PyDict, PyTuple, PyString};
use pyo3::prelude::*;
use pyo3::exceptions::{PyTypeError, PyValueError, PyException, PySyntaxError, PyNameError, PyKeyError, PyOSError, PyImportError};

use crate::eval::{CallableResolver, ResolveFunc};
use crate::object::{Object, FuncVariant, List, Map, Key, Closure, ObjectVariant, IntVariant};
use crate::error::{Error, Reason};


/// Convert a Gold error to a Python error.
pub fn err_to_py(err: Error) -> PyErr {
    match err.reason {
        None => PyException::new_err(err.rendered),
        Some(Reason::None) => PyException::new_err(err.rendered),
        Some(Reason::Syntax(_)) => PySyntaxError::new_err(err.rendered),
        Some(Reason::Unbound(_)) => PyNameError::new_err(err.rendered),
        Some(Reason::Unassigned(_)) => PyKeyError::new_err(err.rendered),
        Some(Reason::Unpack(_)) => PyTypeError::new_err(err.rendered),
        Some(Reason::Internal(_)) => PyException::new_err(err.rendered),
        Some(Reason::External(_)) => PyException::new_err(err.rendered),
        Some(Reason::TypeMismatch(_)) => PyTypeError::new_err(err.rendered),
        Some(Reason::Value(_)) => PyValueError::new_err(err.rendered),
        Some(Reason::FileSystem(_)) => PyOSError::new_err(err.rendered),
        Some(Reason::UnknownImport(_)) => PyImportError::new_err(err.rendered),
    }
}


/// Thin wrapper around [`object::Function`] so that it can be converted to an
/// opaque Python type.
///
/// This type represents all kinds of callable objects.
#[pyclass]
#[derive(Clone)]
pub struct Function(FuncVariant);

#[pymethods]
impl Function {
    #[args(args = "*", kwargs = "**")]
    fn __call__(&self, py: Python<'_>, args: &PyTuple, kwargs: Option<&PyDict>) -> PyResult<Py<PyAny>> {
        let func = Object::func(self.0.clone());

        // Extract positional arguments
        let posargs_obj = args.extract::<Object>()?;
        let posargs = posargs_obj.get_list().ok_or_else(
            || PyTypeError::new_err("internal error py001 - this should not happen, please file a bug report")
        )?;

        // Extract keyword arguments
        let kwargs_obj = kwargs.map(|x| x.extract::<Object>()).transpose()?;
        let result = if let Some(x) = kwargs_obj {
            let gkwargs = x.get_map().ok_or_else(
                || PyTypeError::new_err("internal error py002 - this should not happen, please file a bug report")
            )?;
            func.call(posargs, Some(gkwargs))
        } else {
            func.call(posargs, None)
        }.map_err(err_to_py)?;

        Ok(result.into_py(py))
    }
}


/// Convert Python objects to Gold
impl<'s> FromPyObject<'s> for Object {
    fn extract(obj: &'s PyAny) -> PyResult<Self> {
        // Nothing magical here, just a prioritized list of possible Python types and their Gold equivalents
        if let Ok(Function(x)) = obj.extract::<Function>() {
            Ok(Object::func(x))
        } else if let Ok(x) = obj.extract::<i64>() {
            Ok(Object::int(x))
        } else if let Ok(x) = obj.extract::<BigInt>() {
            Ok(Object::int(x))
        } else if let Ok(x) = obj.extract::<f64>() {
            Ok(Object::from(x))
        } else if let Ok(x) = obj.extract::<&str>() {
            Ok(Object::from(x))
        } else if let Ok(x) = obj.extract::<bool>() {
            Ok(Object::from(x))
        } else if let Ok(x) = obj.extract::<Vec<Object>>() {
            Ok(Object::list(x))
        } else if let Ok(x) = obj.extract::<HashMap<String, Object>>() {
            let mut map = Map::new();
            for (k, v) in x {
                map.insert(Key::new(k), v);
            }
            Ok(Object::map(map))
        } else if obj.is_none() {
            Ok(Object::null())
        } else if obj.is_callable() {
            let func: Py<PyAny> = obj.into();
            let closure = Closure(Arc::new(
                move |args: &List, kwargs: Option<&Map>| {
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
                }
            ));
            Ok(Object::func(closure))
        } else {
            Err(PyTypeError::new_err(
                format!("uncovertible type: {}", obj.get_type().name().unwrap_or("unknown"))
            ))
        }
    }
}


/// Convert Gold objects to Python
impl pyo3::IntoPy<PyObject> for Object {
    fn into_py(self, py: Python<'_>) -> PyObject {
        match self.variant() {
            ObjectVariant::Int(IntVariant::Small(x)) => x.into_py(py),
            ObjectVariant::Int(IntVariant::Big(x)) => x.as_ref().clone().into_py(py),
            ObjectVariant::Float(x) => x.into_py(py),
            ObjectVariant::Str(x) => x.as_str().into_py(py),
            ObjectVariant::Boolean(x) => x.into_py(py),
            ObjectVariant::List(x) => PyList::new(py, x.iter().map(|x| x.clone().into_py(py))).into(),
            ObjectVariant::Map(x) => {
                let r = PyDict::new(py);
                for (k, v) in x.as_ref() {
                    r.set_item(k.as_str(), v.clone().into_py(py)).unwrap();
                }
                r.into()
            },
            ObjectVariant::Null => (None as Option<bool>).into_py(py),
            ObjectVariant::Func(x) => Function(x.clone()).into_py(py),
        }
    }
}


/// Convert Python callables to CallableResolver.
impl<'s> FromPyObject<'s> for CallableResolver {
    fn extract(obj: &'s PyAny) -> PyResult<Self> {
        if obj.is_callable() {
            let func: Py<PyAny> = obj.into();
            let closure = ResolveFunc(Arc::new(
                move |path: &str| {
                    let result = Python::with_gil(|py| {
                        let s = PyString::new(py, path);
                        let a = PyTuple::new(py, vec![s]);
                        let result = func.call(py, a, None).ok()?.extract::<Option<Object>>(py).ok()?;
                        result
                    });
                    result.ok_or_else(Error::default)
                }
            ));
            Ok(CallableResolver { resolver: closure })
        } else {
            Err(PyTypeError::new_err(
                format!("uncovertible type: {}, expected callable", obj.get_type().name().unwrap_or("unknown"))
            ))
        }
    }
}
