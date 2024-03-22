use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

use num_bigint::BigInt;

use pyo3::exceptions::{
    PyException, PyImportError, PyKeyError, PyNameError, PyOSError, PySyntaxError, PyTypeError,
    PyValueError,
};
use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList, PyString, PyTuple};

use crate::error::{Error, Reason};
use crate::eval::ImportConfig as GoldImportConfig;
use crate::object::function::{Closure, FuncVariant};
use crate::object::ObjV;
use crate::{Key, List, Map, Object};

/// Convert a Gold error to a Python error.
pub fn err_to_py(err: Error) -> PyErr {
    let err = err.render(None);
    let pystr = format!("From Gold: {}", err.rendered().unwrap());
    match err.reason() {
        None => PyException::new_err(pystr),
        Some(Reason::None) => PyException::new_err(pystr),
        Some(Reason::Syntax(_)) => PySyntaxError::new_err(pystr),
        Some(Reason::Unbound(_)) => PyNameError::new_err(pystr),
        Some(Reason::Unassigned(_)) => PyKeyError::new_err(pystr),
        Some(Reason::Unpack(_)) => PyTypeError::new_err(pystr),
        Some(Reason::Internal(_)) => PyException::new_err(pystr),
        Some(Reason::External(_)) => PyException::new_err(pystr),
        Some(Reason::TypeMismatch(_)) => PyTypeError::new_err(pystr),
        Some(Reason::Value(_)) => PyValueError::new_err(pystr),
        Some(Reason::FileSystem(_)) => PyOSError::new_err(pystr),
        Some(Reason::UnknownImport(_)) => PyImportError::new_err(pystr),
    }
}

/// Thin wrapper around [`object::Function`] so that it can be converted to an
/// opaque Python type.
///
/// This type represents all kinds of callable objects.
#[pyclass(unsendable)]
#[derive(Clone)]
pub struct Function(FuncVariant);

#[pymethods]
impl Function {
    #[args(args = "*", kwargs = "**")]
    fn __call__(
        &self,
        py: Python<'_>,
        args: &PyTuple,
        kwargs: Option<&PyDict>,
    ) -> PyResult<Py<PyAny>> {
        let func = Object::func(self.0.clone());

        // Extract positional arguments
        let posargs_obj = args.extract::<Object>()?;
        let posargs = posargs_obj.get_list().ok_or_else(|| {
            PyTypeError::new_err(
                "internal error py001 - this should not happen, please file a bug report",
            )
        })?;

        // Extract keyword arguments
        let kwargs_obj = kwargs.map(|x| x.extract::<Object>()).transpose()?;
        let result = if let Some(x) = kwargs_obj {
            let gkwargs = x.get_map().ok_or_else(|| {
                PyTypeError::new_err(
                    "internal error py002 - this should not happen, please file a bug report",
                )
            })?;
            func.call(&*posargs, Some(&*gkwargs))
        } else {
            func.call(&*posargs, None)
        }
        .map_err(err_to_py)?;

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
            let closure = Closure(Rc::new(move |args: &List, kwargs: Option<&Map>| {
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
            }));
            Ok(Object::func(closure))
        } else {
            Err(PyTypeError::new_err(format!(
                "uncovertible type: {}",
                obj.get_type().name().unwrap_or("unknown")
            )))
        }
    }
}

/// Convert Gold objects to Python
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
            ObjV::Func(x) => Function(x.clone()).into_py(py),
        }
    }
}

struct ImportFunction(Rc<dyn Fn(&str) -> Result<Option<Object>, Error>>);

impl<'s> FromPyObject<'s> for ImportFunction {
    fn extract(obj: &'s PyAny) -> PyResult<Self> {
        if obj.is_callable() {
            let func: Py<PyAny> = obj.into();
            let closure = move |path: &str| {
                let result = Python::with_gil(|py| {
                    let pypath = PyString::new(py, path);
                    let pyargs = PyTuple::new(py, vec![pypath]);
                    let result = func.call(py, pyargs, None)?;
                    result.extract::<Option<Object>>(py)
                });

                result.map_err(|err| Error::new(Reason::External(err.to_string())))
            };
            Ok(ImportFunction(Rc::new(closure)))
        } else {
            Err(PyTypeError::new_err(format!(
                "got {}, expected callable",
                obj.get_type().name().unwrap_or("unknown")
            )))
        }
    }
}

/// Python version of the [`ImportConfig`] struct.
#[pyclass(unsendable)]
#[derive(Clone)]
pub struct ImportConfig {
    /// Corresponds to [`ImportConfig::root_path`].
    pub root_path: Option<String>,

    /// Corresponds to [`ImportConfig::custom`].
    pub custom: Option<Rc<dyn Fn(&str) -> Result<Option<Object>, Error>>>,
}

#[pymethods]
impl ImportConfig {
    #[new]
    #[args(root = "None", custom = "None")]
    fn new(root: Option<String>, custom: Option<ImportFunction>) -> Self {
        ImportConfig {
            root_path: root,
            custom: custom.map(|x| x.0),
        }
    }
}

impl ImportConfig {
    /// Convert the Python object to a Rust object.
    pub fn to_gold(&self) -> GoldImportConfig {
        GoldImportConfig {
            root_path: self.root_path.as_ref().map(|x| PathBuf::from(x)),
            custom: self.custom.clone(),
        }
    }
}
