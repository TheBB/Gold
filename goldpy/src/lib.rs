use std::collections::HashMap;
use std::str::FromStr;
use std::sync::Arc;

use num_bigint::BigInt;

use pyo3::types::{PyList, PyDict};
use pyo3::prelude::*;
use pyo3::exceptions::{PyTypeError, PyValueError};

use gold::{object, Object, eval_raw};


struct ObjectWrapper(Object);

#[pyclass]
#[derive(Clone)]
struct Function(Arc<object::Function>);

#[pyclass]
#[derive(Clone)]
struct Builtin(object::Builtin);


impl<'s> FromPyObject<'s> for ObjectWrapper {
    fn extract(obj: &'s PyAny) -> PyResult<Self> {
        if let Ok(Function(x)) = obj.extract::<Function>() {
            Ok(ObjectWrapper(Object::Function(x)))
        } else if let Ok(Builtin(x)) = obj.extract::<Builtin>() {
            Ok(ObjectWrapper(Object::Builtin(x)))
        } else if let Ok(x) = obj.extract::<i64>() {
            Ok(ObjectWrapper(Object::from(x)))
        } else if let Ok(x) = obj.extract::<BigInt>() {
            Ok(ObjectWrapper(Object::bigint(&x.to_string()).unwrap()))
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
        } else {
            Err(PyErr::new::<PyTypeError, _>("what the fuck"))
        }
    }
}

impl pyo3::IntoPy<PyObject> for ObjectWrapper {
    fn into_py(self, py: Python<'_>) -> PyObject {
        match self.0 {
            Object::Integer(x) => x.into_py(py),
            Object::BigInteger(x) => BigInt::from_str(&x.to_string()).unwrap().into_py(py),
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
        }
    }
}


#[pyfunction]
fn eval(x: String) -> PyResult<ObjectWrapper> {
    eval_raw(x.as_str()).map_err(
        |err| PyErr::new::<PyValueError, _>(err)
    ).map(ObjectWrapper)
}


#[pymodule]
fn goldpy(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<Function>()?;
    m.add_class::<Builtin>()?;
    m.add_function(wrap_pyfunction!(eval, m)?)?;
    Ok(())
}
