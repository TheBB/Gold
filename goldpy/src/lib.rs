use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use num_bigint::BigInt;

use pyo3::types::{PyList, PyDict, PyTuple, PyString};
use pyo3::prelude::*;
use pyo3::exceptions::{PyTypeError, PyValueError};

use gold::{object, Object};
use gold::eval::{CallableResolver, ResolveFunc};


struct ObjectWrapper(Object);

struct CallableResolverWrapper(CallableResolver);

#[pyclass]
#[derive(Clone)]
struct Function(Arc<object::Function>);

#[pymethods]
impl Function {
    #[args(args = "*", kwargs = "**")]
    fn __call__(&self, py: Python<'_>, args: &PyTuple, kwargs: Option<&PyDict>) -> PyResult<Py<PyAny>> {
        let gargs: ObjectWrapper = args.extract()?;
        let gkwargs: ObjectWrapper = if let Some(pykwargs) = kwargs {
            pykwargs.extract()?
        } else {
            ObjectWrapper(Object::map(()))
        };

        let result = gold::call_obj(&Object::Function(self.0.clone()), gargs.0, gkwargs.0)
            .map_err(|err| PyErr::new::<PyValueError, _>(err))?;

        Ok(ObjectWrapper(result).into_py(py))
    }
}


#[pyclass]
#[derive(Clone)]
struct Builtin(object::Builtin);

#[pymethods]
impl Builtin {
    #[args(args = "*", kwargs = "**")]
    fn __call__(&self, py: Python<'_>, args: &PyTuple, kwargs: Option<&PyDict>) -> PyResult<Py<PyAny>> {
        let gargs: ObjectWrapper = args.extract()?;
        let gkwargs: ObjectWrapper = if let Some(pykwargs) = kwargs {
            pykwargs.extract()?
        } else {
            ObjectWrapper(Object::map(()))
        };

        let result = gold::call_obj(&Object::Builtin(self.0.clone()), gargs.0, gkwargs.0)
            .map_err(|err| PyErr::new::<PyValueError, _>(err))?;

        Ok(ObjectWrapper(result).into_py(py))
    }
}


#[pyclass]
#[derive(Clone)]
struct Closure(object::Closure);

#[pymethods]
impl Closure {
    #[args(args = "*", kwargs = "**")]
    fn __call__(&self, py: Python<'_>, args: &PyTuple, kwargs: Option<&PyDict>) -> PyResult<Py<PyAny>> {
        let gargs: ObjectWrapper = args.extract()?;
        let gkwargs: ObjectWrapper = if let Some(pykwargs) = kwargs {
            pykwargs.extract()?
        } else {
            ObjectWrapper(Object::map(()))
        };

        let result = gold::call_obj(&Object::Closure(self.0.clone()), gargs.0, gkwargs.0)
            .map_err(|err| PyErr::new::<PyValueError, _>(err))?;

        Ok(ObjectWrapper(result).into_py(py))
    }
}


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
                    result.ok_or_else(|| "dingbob".to_string())
                }
            ));
            Ok(CallableResolverWrapper(CallableResolver { resolver: closure }))
        } else {
            Err(PyErr::new::<PyTypeError, _>("what the fck"))
        }
    }
}


impl<'s> FromPyObject<'s> for ObjectWrapper {
    fn extract(obj: &'s PyAny) -> PyResult<Self> {
        if let Ok(Function(x)) = obj.extract::<Function>() {
            Ok(ObjectWrapper(Object::Function(x)))
        } else if let Ok(Builtin(x)) = obj.extract::<Builtin>() {
            Ok(ObjectWrapper(Object::Builtin(x)))
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
                map.insert(Arc::new(k), v.0.clone());
            }
            Ok(ObjectWrapper(Object::Map(Arc::new(map))))
        } else if obj.is_none() {
            Ok(ObjectWrapper(Object::Null))
        } else if obj.is_callable() {
            let func: Py<PyAny> = obj.into();
            let closure: object::Closure = object::Closure(Arc::new(
                move |args: &object::List, kwargs: &object::Map| {
                    let result = Python::with_gil(|py| {
                        let a = PyTuple::new(py, args.iter().map(|x| ObjectWrapper(x.clone()).into_py(py)));
                        let b = PyDict::new(py);
                        for (k, v) in kwargs {
                            b.set_item(k.as_ref(), ObjectWrapper(v.clone()).into_py(py))?;
                        }
                        let result = func.call(py, a, Some(b))?.extract::<ObjectWrapper>(py)?;
                        Ok(result.0)
                    });
                    result.map_err(|err: PyErr| err.to_string())
                }
            ));
            Ok(ObjectWrapper(Object::Closure(closure)))
        } else {
            Err(PyErr::new::<PyTypeError, _>("what the fuck"))
        }
    }
}

impl pyo3::IntoPy<PyObject> for ObjectWrapper {
    fn into_py(self, py: Python<'_>) -> PyObject {
        match self.0 {
            Object::Integer(x) => x.into_py(py),
            Object::BigInteger(x) => x.as_ref().clone().into_py(py),
            Object::Float(x) => x.into_py(py),
            Object::String(x) => x.as_ref().into_py(py),
            Object::Boolean(x) => x.into_py(py),
            Object::List(x) => PyList::new(py, x.iter().map(|x| ObjectWrapper(x.clone()).into_py(py))).into(),
            Object::Map(x) => {
                let r = PyDict::new(py);
                for (k, v) in x.as_ref() {
                    r.set_item(k.as_ref(), ObjectWrapper(v.clone()).into_py(py)).unwrap();
                }
                r.into()
            },
            Object::Null => (None as Option<bool>).into_py(py),
            Object::Function(x) => Function(x).into_py(py),
            Object::Builtin(x) => Builtin(x).into_py(py),
            Object::Closure(x) => Closure(x).into_py(py),
        }
    }
}


#[pyfunction]
fn eval(x: String, path: Option<String>, resolver: CallableResolverWrapper) -> PyResult<ObjectWrapper> {
    gold::eval(
        x.as_ref(),
        path.map(PathBuf::from).as_ref().map(PathBuf::as_ref),
        &resolver.0,
    ).map_err(
        |err| PyErr::new::<PyValueError, _>(err)
    ).map(ObjectWrapper)
}


#[pyfunction]
fn eval_raw(x: String) -> PyResult<ObjectWrapper> {
    gold::eval_raw(
        x.as_str(),
    ).map_err(
        |err| PyErr::new::<PyValueError, _>(err)
    ).map(ObjectWrapper)
}


#[pyfunction]
fn eval_file(x: String) -> PyResult<ObjectWrapper> {
    gold::eval_file(
        &PathBuf::from(x)
    ).map_err(
        |err| PyErr::new::<PyValueError, _>(err)
    ).map(ObjectWrapper)
}


#[pymodule]
fn goldpy(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<Function>()?;
    m.add_class::<Builtin>()?;
    m.add_function(wrap_pyfunction!(eval, m)?)?;
    m.add_function(wrap_pyfunction!(eval_raw, m)?)?;
    m.add_function(wrap_pyfunction!(eval_file, m)?)?;
    Ok(())
}
