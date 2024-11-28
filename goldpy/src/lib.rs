use std::path::PathBuf;

use pyo3::prelude::*;

use gold::{Object, PyImportConfig, Error};

#[pyfunction]
fn eval(x: String, resolver: PyImportConfig) -> PyResult<Object> {
    gold::eval(x.as_ref(), &resolver.to_gold()).map_err(Error::to_py)
}

#[pyfunction]
fn eval_raw(x: String) -> PyResult<Object> {
    gold::eval_raw(x.as_str()).map_err(Error::to_py)
}

#[pyfunction]
fn eval_file(x: String) -> Object {
    gold::eval_file(&PathBuf::from(x)).map_err(Error::to_py).unwrap()
}

#[pymodule]
fn goldpy<'py>(_py: Python<'py>, m: &Bound<'py, PyModule>) -> PyResult<()> {
    m.add_class::<PyImportConfig>()?;
    m.add_function(wrap_pyfunction!(eval, m)?)?;
    m.add_function(wrap_pyfunction!(eval_raw, m)?)?;
    m.add_function(wrap_pyfunction!(eval_file, m)?)?;
    Ok(())
}
