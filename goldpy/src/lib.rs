use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use gold::object::IntVariant;
use num_bigint::BigInt;

use pyo3::types::{PyList, PyDict, PyTuple, PyString};
use pyo3::prelude::*;
use pyo3::exceptions::{PyTypeError, PyValueError, PyException, PySyntaxError, PyNameError, PyKeyError, PyOSError, PyImportError};

use gold::{object, Object};
use gold::error::{Error, Reason};
use gold::eval::{CallableResolver, ResolveFunc};


/// Thin wrapper around [`object::Function`] so that it can be converted to an
/// opaque Python type.
///
/// This type represents all kinds of callable objects.
#[pyclass]
#[derive(Clone)]
struct Function(object::FuncVariant);

#[pymethods]
impl Function {
    #[args(args = "*", kwargs = "**")]
    fn __call__(&self, py: Python<'_>, args: &PyTuple, kwargs: Option<&PyDict>) -> PyResult<Py<PyAny>> {
        call(py, &Object::function(self.0.clone()), args, kwargs)
    }
}


/// Convert a Gold error to a Python error.
fn err_to_py(err: Error) -> PyErr {
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


/// General function for calling a Gold function with Python arguments.
fn call(py: Python<'_>, func: &Object, args: &PyTuple, kwargs: Option<&PyDict>) -> PyResult<Py<PyAny>> {

    // Extract positional arguments
    let posargs_obj = args.extract::<ObjectWrapper>()?.0;
    let posargs = posargs_obj.get_list().ok_or_else(
        || PyTypeError::new_err("internal error py001 - this should not happen, please file a bug report")
    )?;

    // Extract keyword arguments
    let kwargs_obj = kwargs.map(|x| x.extract::<ObjectWrapper>()).transpose()?.map(|x| x.0);
    let result = if let Some(x) = kwargs_obj {
        let gkwargs = x.get_map().ok_or_else(
            || PyTypeError::new_err("internal error py002 - this should not happen, please file a bug report")
        )?;
        func.call(posargs, Some(gkwargs))
    } else {
        func.call(posargs, None)
    }.map_err(err_to_py)?;

    Ok(ObjectWrapper(result).into_py(py))
}


/// Thin wrapper around Object for converting to and from Python.
struct ObjectWrapper(Object);


/// Convert Python objects to Gold
impl<'s> FromPyObject<'s> for ObjectWrapper {
    fn extract(obj: &'s PyAny) -> PyResult<Self> {
        // Nothing magical here, just a prioritized list of possible Python types and their Gold equivalents
        if let Ok(Function(x)) = obj.extract::<Function>() {
            Ok(ObjectWrapper(Object::Func(x)))
        } else if let Ok(x) = obj.extract::<i64>() {
            Ok(ObjectWrapper(Object::from(x)))
        } else if let Ok(x) = obj.extract::<BigInt>() {
            Ok(ObjectWrapper(Object::from(x)))
        } else if let Ok(x) = obj.extract::<f64>() {
            Ok(ObjectWrapper(Object::from(x)))
        } else if let Ok(x) = obj.extract::<&str>() {
            Ok(ObjectWrapper(Object::from(x)))
        } else if let Ok(x) = obj.extract::<bool>() {
            Ok(ObjectWrapper(Object::from(x)))
        } else if let Ok(x) = obj.extract::<Vec<ObjectWrapper>>() {
            Ok(ObjectWrapper(Object::List(Arc::new(x.iter().map(|x| x.0.clone()).collect()))))
        } else if let Ok(x) = obj.extract::<HashMap<String, ObjectWrapper>>() {
            let mut map = object::Map::new();
            for (k, v) in x {
                map.insert(object::Key::new(k), v.0.clone());
            }
            Ok(ObjectWrapper(Object::Map(Arc::new(map))))
        } else if obj.is_none() {
            Ok(ObjectWrapper(Object::Null))
        } else if obj.is_callable() {
            let func: Py<PyAny> = obj.into();
            let closure: object::Closure = object::Closure(Arc::new(
                move |args: &object::List, kwargs: Option<&object::Map>| {
                    let result = Python::with_gil(|py| {
                        let a = PyTuple::new(py, args.iter().map(|x| ObjectWrapper(x.clone()).into_py(py)));
                        let b = PyDict::new(py);
                        if let Some(kws) = kwargs {
                            for (k, v) in kws {
                                b.set_item(k.as_str(), ObjectWrapper(v.clone()).into_py(py))?;
                            }
                        }
                        let result = func.call(py, a, Some(b))?.extract::<ObjectWrapper>(py)?;
                        Ok(result.0)
                    });
                    result.map_err(|e: PyErr| Error::new(Reason::External(format!("{}", e))))
                }
            ));
            Ok(ObjectWrapper(Object::function(closure)))
        } else {
            Err(PyTypeError::new_err(
                format!("uncovertible type: {}", obj.get_type().name().unwrap_or("unknown"))
            ))
        }
    }
}


/// Convert Gold objects to Python
impl pyo3::IntoPy<PyObject> for ObjectWrapper {
    fn into_py(self, py: Python<'_>) -> PyObject {
        match self.0 {
            Object::Int(IntVariant::Small(x)) => x.into_py(py),
            Object::Int(IntVariant::Big(x)) => x.as_ref().clone().into_py(py),
            Object::Float(x) => x.into_py(py),
            Object::Str(x) => x.as_str().into_py(py),
            Object::Boolean(x) => x.into_py(py),
            Object::List(x) => PyList::new(py, x.iter().map(|x| ObjectWrapper(x.clone()).into_py(py))).into(),
            Object::Map(x) => {
                let r = PyDict::new(py);
                for (k, v) in x.as_ref() {
                    r.set_item(k.as_str(), ObjectWrapper(v.clone()).into_py(py)).unwrap();
                }
                r.into()
            },
            Object::Null => (None as Option<bool>).into_py(py),
            Object::Func(x) => Function(x).into_py(py),
        }
    }
}


/// Thin wrapper around CallableResolver for converting from Python (but not to Python).
struct CallableResolverWrapper(CallableResolver);


/// Convert Python callables to CallableResolver.
impl<'s> FromPyObject<'s> for CallableResolverWrapper {
    fn extract(obj: &'s PyAny) -> PyResult<Self> {
        if obj.is_callable() {
            let func: Py<PyAny> = obj.into();
            let closure = ResolveFunc(Arc::new(
                move |path: &str| {
                    let result = Python::with_gil(|py| {
                        let s = PyString::new(py, path);
                        let a = PyTuple::new(py, vec![s]);
                        let result = func.call(py, a, None).ok()?.extract::<Option<ObjectWrapper>>(py).ok()?;
                        result.map(|x| x.0)
                    });
                    result.ok_or_else(Error::default)
                }
            ));
            Ok(CallableResolverWrapper(CallableResolver { resolver: closure }))
        } else {
            Err(PyTypeError::new_err(
                format!("uncovertible type: {}, expected callable", obj.get_type().name().unwrap_or("unknown"))
            ))
        }
    }
}


#[pyfunction]
fn eval(x: String, path: Option<String>, resolver: CallableResolverWrapper) -> PyResult<ObjectWrapper> {
    gold::eval(
        x.as_ref(),
        path.map(PathBuf::from).as_ref().map(PathBuf::as_ref),
        &resolver.0,
    ).map_err(err_to_py).map(ObjectWrapper)
}


#[pyfunction]
fn eval_raw(x: String) -> PyResult<ObjectWrapper> {
    gold::eval_raw(
        x.as_str(),
    ).map_err(err_to_py).map(ObjectWrapper)
}


#[pyfunction]
fn eval_file(x: String) -> PyResult<ObjectWrapper> {
    gold::eval_file(
        &PathBuf::from(x)
    ).map_err(err_to_py).map(ObjectWrapper)
}


#[pymodule]
fn goldpy(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<Function>()?;
    m.add_function(wrap_pyfunction!(eval, m)?)?;
    m.add_function(wrap_pyfunction!(eval_raw, m)?)?;
    m.add_function(wrap_pyfunction!(eval_file, m)?)?;
    Ok(())
}
