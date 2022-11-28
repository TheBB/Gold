#![feature(is_some_and)]

#[macro_use]
extern crate lazy_static;

mod ast;
mod builtins;
pub mod error;
pub mod eval;
mod parsing;
mod traits;
mod util;

pub mod object;

#[cfg(test)]
mod tests;

use std::fs::read_to_string;
use std::path::Path;

use error::Error;
use eval::{ImportResolver, NullResolver};
pub use object::Object;
pub use parsing::parse;


pub fn eval<T: ImportResolver>(input: &str, root: Option<&Path>, resolver: &T) -> Result<Object, Error> {
    if let Some(path) = root {
        parsing::parse(input).and_then(|file| eval::eval_path(&file, &path, resolver))
    } else {
        parsing::parse(input).and_then(|file| eval::eval_raw(&file, resolver))
    }
}


pub fn eval_raw(input: &str) -> Result<Object, Error> {
    eval(input, None, &NullResolver {})
}


pub fn eval_file(input: &Path) -> Result<Object, Error> {
    let contents = read_to_string(input).map_err(|_| Error::default())?;
    eval(&contents, Some(input), &NullResolver {})
}
