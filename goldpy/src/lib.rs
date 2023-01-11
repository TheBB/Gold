use std::path::PathBuf;

use pyo3::prelude::*;

use gold::{Object};
use gold::python::{err_to_py, Function, ImportConfig};


#[pyfunction]
fn eval(x: String, resolver: ImportConfig) -> PyResult<Object> {
    gold::eval(x.as_ref(), &resolver.to_gold()).map_err(err_to_py)
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
    m.add_class::<ImportConfig>()?;
    m.add_function(wrap_pyfunction!(eval, m)?)?;
    m.add_function(wrap_pyfunction!(eval_raw, m)?)?;
    m.add_function(wrap_pyfunction!(eval_file, m)?)?;
    Ok(())
}
