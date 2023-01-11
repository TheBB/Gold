use std::path::PathBuf;

use pyo3::prelude::*;

use gold::{CallableResolver, Object};
use gold::python::{err_to_py, Function};


#[pyfunction]
fn eval(x: String, path: Option<String>, resolver: CallableResolver) -> PyResult<Object> {
    gold::eval(
        x.as_ref(),
        path.map(PathBuf::from).as_ref().map(PathBuf::as_ref),
        &resolver,
    ).map_err(err_to_py)
}


#[pyfunction]
fn eval_raw(x: String) -> PyResult<Object> {
    gold::eval_raw(
        x.as_str(),
    ).map_err(err_to_py)
}


#[pyfunction]
fn eval_file(x: String) -> PyResult<Object> {
    gold::eval_file(
        &PathBuf::from(x)
    ).map_err(err_to_py)
}


#[pymodule]
fn goldpy(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<Function>()?;
    m.add_function(wrap_pyfunction!(eval, m)?)?;
    m.add_function(wrap_pyfunction!(eval_raw, m)?)?;
    m.add_function(wrap_pyfunction!(eval_file, m)?)?;
    Ok(())
}
